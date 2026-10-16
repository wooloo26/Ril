param([string]$Executable, [string]$Source, [string]$Budget, [string]$OutputDirectory)
$ErrorActionPreference = 'Stop'
# Install the job on this dedicated helper before spawning the compiler. Child
# processes inherit the job, so parsing cannot race with limit installation.
Add-Type @'
using System;
using System.Runtime.InteropServices;
public static class StaticJob {
  [StructLayout(LayoutKind.Sequential)] public struct Basic {
    public long ProcessTime,JobTime; public uint Flags;
    public UIntPtr MinWork,MaxWork; public uint Active; public UIntPtr Affinity;
    public uint Priority,Scheduling;
  }
  [StructLayout(LayoutKind.Sequential)] public struct Io {
    public ulong ReadOps,WriteOps,OtherOps,ReadBytes,WriteBytes,OtherBytes;
  }
  [StructLayout(LayoutKind.Sequential)] public struct Limits {
    public Basic Basic; public Io Io; public UIntPtr ProcessMemory,JobMemory,PeakProcess,PeakJob;
  }
  [DllImport("kernel32.dll",CharSet=CharSet.Unicode,SetLastError=true)] public static extern IntPtr CreateJobObject(IntPtr attributes,string name);
  [DllImport("kernel32.dll",SetLastError=true)] public static extern bool SetInformationJobObject(IntPtr job,int kind,ref Limits information,uint size);
  [DllImport("kernel32.dll",SetLastError=true)] public static extern bool QueryInformationJobObject(IntPtr job,int kind,ref Limits information,uint size,IntPtr returned);
  [DllImport("kernel32.dll",SetLastError=true)] public static extern bool AssignProcessToJobObject(IntPtr job,IntPtr process);
  [DllImport("kernel32.dll")] public static extern IntPtr GetCurrentProcess();
  [DllImport("kernel32.dll")] public static extern bool CloseHandle(IntPtr handle);
}
'@
function Quote-Argument([string]$Value) {
    '"' + [regex]::Replace([regex]::Replace($Value, '(\\*)"', '$1$1\"'), '(\\+)$', '$1$1') + '"'
}
$job = [StaticJob]::CreateJobObject([IntPtr]::Zero, $null)
$limits = New-Object StaticJob+Limits
$basic = New-Object StaticJob+Basic
$basic.Flags = 0x100 # JOB_OBJECT_LIMIT_PROCESS_MEMORY
$limits.Basic = $basic
$limits.ProcessMemory = [UIntPtr]::new(536870912)
$size = [Runtime.InteropServices.Marshal]::SizeOf($limits)
$child = $null
try {
    if (-not [StaticJob]::SetInformationJobObject($job, 9, [ref]$limits, $size)) { throw 'Cannot install the 512 MiB process limit' }
    $observed = New-Object StaticJob+Limits
    if (-not [StaticJob]::QueryInformationJobObject($job, 9, [ref]$observed, $size, [IntPtr]::Zero) -or $observed.Basic.Flags -ne 0x100 -or $observed.ProcessMemory.ToUInt64() -ne 536870912) { throw 'Memory limit read-back failed' }
    if (-not [StaticJob]::AssignProcessToJobObject($job, [StaticJob]::GetCurrentProcess())) { throw 'Cannot assign the helper to its memory-limited job' }
    $stdout = Join-Path $OutputDirectory 'bounded.stdout.json'
    $stderr = Join-Path $OutputDirectory 'bounded.stderr.log'
    $arguments = @('check', $Source, '--json', '--static-budget', $Budget) | ForEach-Object { Quote-Argument $_ }
    $watch = [Diagnostics.Stopwatch]::StartNew()
    $child = Start-Process -FilePath $Executable -ArgumentList ($arguments -join ' ') -WindowStyle Hidden -PassThru -RedirectStandardOutput $stdout -RedirectStandardError $stderr
    # Windows PowerShell otherwise opens the handle only after the short-lived
    # process is gone, leaving ExitCode null despite complete redirected output.
    $null = $child.Handle
    $finished = $child.WaitForExit(20000)
    if (-not $finished) { Stop-Process -Id $child.Id -Force }
    $child.WaitForExit()
    $final = New-Object StaticJob+Limits
    if (-not [StaticJob]::QueryInformationJobObject($job, 9, [ref]$final, $size, [IntPtr]::Zero)) { throw 'Cannot read peak process memory' }
    [pscustomobject]@{
        exit = $child.ExitCode
        timeout = -not $finished
        milliseconds = $watch.ElapsedMilliseconds
        peak_process_commit_bytes = $final.PeakProcess.ToUInt64()
        memory_limit_bytes = $observed.ProcessMemory.ToUInt64()
        verified_job_flags = $observed.Basic.Flags
        stdout = [IO.File]::ReadAllText($stdout)
        stderr = [IO.File]::ReadAllText($stderr)
    } | ConvertTo-Json -Compress
} finally {
    if ($null -ne $child -and -not $child.HasExited) { Stop-Process -Id $child.Id -Force }
    [void][StaticJob]::CloseHandle($job)
}
