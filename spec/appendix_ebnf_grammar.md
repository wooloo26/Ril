# Appendix: Consolidated Formal EBNF Grammar

This appendix provides the complete, consolidated, machine-readable context-free grammar for Ril in Extended Backus-Naur Form (EBNF), designed for direct compiler and parser generation.

---

## 1. Complete EBNF Grammar Specification

```ebnf
(* ========================================================================= *)
(* 1. Lexical Grammar                                                        *)
(* ========================================================================= *)

Identifier          ::= ( UnicodeLetter { IdentifierContinue } )
                      | ( "_" IdentifierContinue { IdentifierContinue } )
IdentifierStart     ::= "_" | UnicodeLetter
IdentifierContinue  ::= UnicodeLetter | Digit | "_"
UnicodeLetter       ::= (* Any Unicode character in Category Lu, Ll, Lt, Lm, Lo *)
UnicodeScalar       ::= (* Any Unicode scalar value U+0000..U+D7FF or U+E000..U+10FFFF *)
Digit               ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
HexDigit            ::= Digit | "a" | "b" | "c" | "d" | "e" | "f" | "A" | "B" | "C" | "D" | "E" | "F"
OctalDigit          ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7"
BinaryDigit         ::= "0" | "1"

DecimalDigits       ::= Digit { [ "_" ] Digit }
DecimalIndex        ::= Digit { Digit }
HexDigits           ::= "0x" HexDigit { [ "_" ] HexDigit }
OctalDigits         ::= "0o" OctalDigit { [ "_" ] OctalDigit }
BinaryDigits        ::= "0b" BinaryDigit { [ "_" ] BinaryDigit }
ExponentPart        ::= ( "e" | "E" ) [ "+" | "-" ] DecimalDigits

Newline             ::= (* Line feed LF (U+000A) or carriage return CR (U+000D) *)
LineCharacter       ::= (* Any character except LF or CR *)
Comment             ::= "--" { LineCharacter }

PathSegment         ::= Identifier | "super"
QualifiedName       ::= PathSegment { "::" Identifier }
ModulePath          ::= [ "./" | "../" { "../" } ] PathSegment { "/" Identifier }

NumericSuffix       ::= "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
FloatSuffix         ::= "f32" | "f64"
IntegerLiteral      ::= ( DecimalDigits | HexDigits | OctalDigits | BinaryDigits ) [ NumericSuffix ]
FloatLiteral        ::= DecimalDigits "." DecimalDigits [ ExponentPart ] [ FloatSuffix ]

ByteLiteral         ::= "b'" ( ByteCharacter | ByteEscape ) "'"
ByteCharacter       ::= (* Any ASCII character except single quote, backslash, LF, or CR *)
ByteEscape          ::= "\" ( "n" | "r" | "t" | "\" | "'" | '"' | "0" | "x" HexDigit HexDigit )
ByteStringLiteral   ::= 'b"' { ByteStringCharacter | ByteEscape } '"'
ByteStringCharacter ::= (* Any ASCII character except double quote, backslash, LF, or CR *)

StringCharacter     ::= (* Any Unicode scalar except double quote, backslash, '{', or '}' *)
StringEscape        ::= "\" ( "n" | "r" | "t" | "\" | '"' | "0" | "{" | "}" | "u{" HexDigit { HexDigit } "}" )
PlainStringLiteral  ::= '"' { StringCharacter | StringEscape } '"'
StringLiteral       ::= '"' { StringCharacter | StringEscape | Interpolation } '"'
Interpolation       ::= "{" Expression [ ":" FormatSpec ] "}"
FormatSpec          ::= [ "0" DecimalDigits ] ( "x" | "X" | "b" | "o" ) | "0" DecimalDigits | "." DecimalDigits "f"

Backtick            ::= "`"
RawStringLiteral    ::= Backtick { RawCharacter } Backtick
RawCharacter        ::= (* Any character except backtick; no escape processing *)
RegexLiteral        ::= 'reg"' { RegexCharacter } '"'
RegexCharacter      ::= "\" UnicodeScalar | (* Any Unicode scalar except double quote or backslash *)

LiteralType         ::= [ "-" ] ( IntegerLiteral | FloatLiteral )
                      | ByteLiteral | PlainStringLiteral | RawStringLiteral
                      | "true" | "false"

(* ========================================================================= *)
(* 2. Types, Kinds, and Universes                                            *)
(* ========================================================================= *)

SourceFile          ::= { Separator } [ Item { Separators Item } [ Separators ] ]
TypeReference       ::= QualifiedName [ GenericApplication ] { "." Identifier [ GenericApplication ] }
InstantiatedMember  ::= QualifiedName GenericApplication "::" Identifier
GenericApplication  ::= "<" GenericArgs ">"
GenericArgs         ::= GenericArg { "," GenericArg } [ "," ]
GenericArg          ::= "{" Expression "}" | ContractArgument | TypeExpression

GenericParameter    ::= "@" Identifier | "&" Identifier | Identifier [ KindSlots ] [ ":" TypeExpression ]
KindSlots           ::= "<" "_" { "," "_" } ">"
GenericParameters   ::= "<" GenericParameter { "," GenericParameter } [ "," ] ">"

WhereClause         ::= "where" Constraint { "," Constraint }
Constraint          ::= TypeExpression ( "=" | "<:" ) TypeExpression
                      | Identifier "lacks" PlainStringLiteral

TypeExpression      ::= FunctionType | TypeIf | TypeMatch | TypeBlock | UnionType
UnionType           ::= PrefixType { "|" PrefixType }
PrefixType          ::= "?" PrefixType | "[" "]" PrefixType | "keyof" PrefixType | PostfixType
PostfixType         ::= PrimaryType { "[" Expression "]" }
PrimaryType         ::= PrimitiveType | TypeReference | RecordType | TupleType | LiteralType
                      | "_" | "(" TypeExpression ")" | "typeof" Expression | TypeCall

PrimitiveType       ::= "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
                      | "int" | "bigint" | "f32" | "f64" | "bool" | "str" | "bytes" | "never"

TypeCall            ::= QualifiedName [ "::" GenericApplication ] ArgumentsCall
TypeBlock           ::= "{" { LetDecl Separators } TypeExpression [ Separators ] "}"
TypeIf              ::= "if" Expression "{" TypeExpression "}" "else" "{" TypeExpression "}"
TypeMatch           ::= "match" "type" TypeExpression "{" TypeMatchArm { "," TypeMatchArm } [ "," ] "}"
TypeMatchArm        ::= TypePattern "->" TypeExpression
TypePattern         ::= "infer" Identifier | "_" | "never" | LiteralType | TypePatternRef
                      | "?" TypePattern | "[" "]" TypePattern
                      | "(" TypePattern "," [ TypePattern { "," TypePattern } [ "," ] ] ")"
                      | "(" ")" | RecordTypePattern | FunctionTypePattern
TypePatternRef      ::= QualifiedName [ "<" TypePattern { "," TypePattern } [ "," ] ">" ]
RecordTypePattern   ::= "{" [ PatternTypeField { "," PatternTypeField } [ "," ] ] "}"
PatternTypeField    ::= [ "mut" | "erased" ] Identifier ":" TypePattern
PatternCallableParam::= [ "mut" | "erased" ] TypePattern
FunctionTypePattern ::= [ "halt" ] "fn" "(" [ PatternCallableParam { "," PatternCallableParam } [ "," ] ] ")"
                        "->" TypePattern { ContractArgument }

TupleType           ::= "(" TypeExpression "," [ TypeExpression { "," TypeExpression } [ "," ] ] ")" | "(" ")"
RecordType          ::= "{" [ RecordTypeEntry { "," RecordTypeEntry } [ "," ] ] "}"
RecordTypeEntry     ::= RecordTypeField | MappedTypeField | RecordTypeSpread | RowTail
RecordTypeSpread    ::= "..." TypeExpression
RowTail             ::= ".." [ Identifier | "_" ]
RecordTypeField     ::= [ "mut" | "erased" ] Identifier ":" TypeExpression [ "=" Expression ]
MappedTypeField     ::= [ "mut" ] "[" Identifier "in" "keyof" TypeExpression
                        [ "if" Expression ] [ "as" Expression ] "]" ":" TypeExpression [ "=" Expression ]

CallableParamType   ::= [ "mut" | "erased" ] ( Identifier ":" TypeExpression | TypeExpression )
FunctionType        ::= [ "halt" ] "fn" [ GenericParameters ] "("
                        [ CallableParamType { "," CallableParamType } [ "," ] ] ")"
                        "->" TypeExpression { ContractArgument } [ WhereClause ]

(* ========================================================================= *)
(* 3. Declarations and Items                                                 *)
(* ========================================================================= *)

Item                ::= LetDecl | FunctionDecl | SumTypeDecl | NominalDecl
                      | OpaqueDecl | TypeAliasDecl | EffectDecl | EffectAliasDecl
                      | ModuleDecl | UseDecl | TestDecl

LetModifier         ::= "scoped" | "view"
LetDecl             ::= [ "pub" ] "let" [ LetModifier ] Pattern [ ":" TypeExpression ] [ "=" Expression ] [ "else" Block ]
Parameter           ::= [ "mut" | "erased" ] Identifier [ ":" TypeExpression ] [ "=" Expression ]
ParameterList       ::= Parameter { "," Parameter } [ "," ]

FunctionSignature   ::= [ "halt" ] "fn" Identifier [ GenericParameters ] "(" [ ParameterList ] ")"
                        [ "->" TypeExpression ] { ContractArgument } [ WhereClause ]
FunctionDecl        ::= [ "pub" ] FunctionSignature Block

SumTypeDecl         ::= [ "pub" ] "type" Identifier [ GenericParameters ] [ WhereClause ]
                        "{" VariantDecl { "," VariantDecl } [ "," ] "}"
VariantDecl         ::= Identifier [ GenericParameters ]
                        [ "(" VariantFields ")" | "{" StructFields "}" ] [ "->" TypeExpression ]
VariantFields       ::= VariantField { "," VariantField } [ "," ]
VariantField        ::= [ "erased" ] Identifier ":" TypeExpression | TypeExpression
StructFields        ::= RecordTypeField { "," RecordTypeField } [ "," ]

NominalDecl         ::= [ "pub" ] "type" Identifier [ GenericParameters ] "(" VariantFields ")" [ WhereClause ]
OpaqueDecl          ::= [ "pub" ] "opaque" "type" Identifier [ GenericParameters ] [ WhereClause ] "=" TypeExpression
TypeAliasDecl       ::= [ "pub" ] "type" Identifier [ GenericParameters ] [ WhereClause ] "=" TypeExpression

EffectItem          ::= QualifiedName
EffectItems         ::= EffectItem { "," EffectItem } [ "," ]
EffectArgument      ::= "@" ( QualifiedName | "{" [ EffectItems ] "}" )
EffectOpDecl        ::= Identifier ":" FunctionType
EffectOperations    ::= EffectOpDecl { "," EffectOpDecl } [ "," ]
EffectDecl          ::= [ "pub" ] "effect" Identifier [ GenericParameters ] "{" EffectOperations "}"
EffectAliasDecl     ::= [ "pub" ] "effect" Identifier "=" "{" [ EffectItems ] "}"

StateItem           ::= "^" "mut" [ Identifier ] | "capture" | "mut" [ Identifier ] | Identifier
StateItems          ::= StateItem { "," StateItem } [ "," ]
StateArgument       ::= "&" ( "mut" | "^" "mut" | "capture" | "{" [ StateItems ] "}" )
ContractArgument    ::= EffectArgument | StateArgument

ModuleDecl          ::= [ "pub" ] "module" Identifier "{" { Separator } [ Item { Separators Item } [ Separators ] ] "}"
UseItemList         ::= UseItem { "," UseItem } [ "," ]
UseItem             ::= Identifier [ "as" Identifier ]
UseDecl             ::= [ "pub" ] "use" ModulePath [ "::" ( "*" | "{" UseItemList "}" | Identifier ) ] [ "as" Identifier ]
TestDecl            ::= "test" StringLiteral Block

(* ========================================================================= *)
(* 4. Blocks, Block Items, and Handlers                                      *)
(* ========================================================================= *)

Separator           ::= ";" | Newline
Separators          ::= Separator { Separator }
BlockItem           ::= Item | Expression
Block               ::= "{" { Separator } [ BlockItem { Separators BlockItem } [ Separators ] ] [ WhereBlock ] "}"
WhereBlock          ::= "where" { Separator } FunctionDecl { Separators FunctionDecl } [ Separators ]

HandlerArm          ::= QualifiedName "(" [ PatternList ] ")" "->" Expression
HandlerSpec         ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
WithExpr            ::= "with" HandlerSpec

AssignTarget        ::= QualifiedName { MemberAccess | TupleIndex | IndexExpr }
CompoundAssignOp    ::= "+=" | "-=" | "*=" | "/=" | "%=" | "+%=" | "-%=" | "*%="
                      | "&=" | "^=" | "|=" | "<<=" | ">>="
AssignmentOp        ::= "=" | CompoundAssignOp

(* ========================================================================= *)
(* 5. Patterns                                                               *)
(* ========================================================================= *)

Pattern             ::= SinglePattern { "|" SinglePattern } [ "as" [ "mut" ] Identifier ]
SinglePattern       ::= [ "mut" ] ( LiteralPattern | RangePattern | NamePattern | RecordPattern | TuplePattern | ArrayPattern | WildcardPattern )
LiteralPattern      ::= LiteralType
NamePattern         ::= QualifiedName [ "(" [ PatternList ] ")" ]
WildcardPattern     ::= "_"
PatternList         ::= Pattern { "," Pattern } [ "," ]
RangePattern        ::= LiteralPattern ( ".." | "..=" ) LiteralPattern
ArrayRestPattern    ::= "..." [ "mut" ] [ Identifier ]
ArrayPattern        ::= "[" [ ( Pattern | ArrayRestPattern ) { "," ( Pattern | ArrayRestPattern ) } [ "," ] ] "]"
RecordPatternField  ::= [ "mut" ] Identifier [ ":" Pattern ]
RecordPattern       ::= [ TypeReference ] ".{" [ ( RecordPatternField | ".." ) { "," ( RecordPatternField | ".." ) } [ "," ] ] "}"
TuplePattern        ::= "(" Pattern "," [ Pattern { "," Pattern } [ "," ] ] ")" | "(" ")"
MatchArm            ::= Pattern [ "if" Expression ] "->" Expression
MatchExpr           ::= "match" Expression "{" [ MatchArm { "," MatchArm } [ "," ] ] "}"

(* ========================================================================= *)
(* 6. Expressions and Precedence Hierarchy                                   *)
(* ========================================================================= *)

Expression          ::= FallbackExpr | AssignTarget AssignmentOp FallbackExpr
FallbackExpr        ::= PipelineExpr [ "??" FallbackExpr ]
PipelineExpr        ::= LogicalOrExpr { "|>" PipelineStage } | MutatingPipeline
MutatingPipeline    ::= AssignTarget "!>" PipelineStage
PipelineStage       ::= StageCallee [ ArgumentsCall ] [ LambdaExpr ] { PostfixTry } | LambdaExpr | AccessorExpr
StageCallee         ::= ( InstantiatedMember | QualifiedName | "(" Expression ")" )
                        { MemberAccess | TupleIndex | IndexExpr } [ "::" GenericApplication ]

LogicalOrExpr       ::= LogicalAndExpr { "||" LogicalAndExpr }
LogicalAndExpr      ::= EqualityExpr { "&&" EqualityExpr }
EqualityExpr        ::= RelationalExpr { ( "==" | "!=" ) RelationalExpr }
RelationalExpr      ::= RangeExpr [ ( "<" | "<=" | ">" | ">=" ) RangeExpr | "is" QualifiedName | "in" TypeExpression ]
RangeExpr           ::= BitOrExpr [ ( ".." | "..=" ) BitOrExpr ]
BitOrExpr           ::= BitXorExpr { "|" BitXorExpr }
BitXorExpr          ::= BitAndExpr { "^" BitAndExpr }
BitAndExpr          ::= ShiftExpr { "&" ShiftExpr }
ShiftExpr           ::= AdditiveExpr { ( "<<" | ">>" ) AdditiveExpr }
AdditiveExpr        ::= MultiplicativeExpr { ( "+" | "-" | "+%" | "-%" ) MultiplicativeExpr }
MultiplicativeExpr  ::= UnaryExpr { ( "*" | "/" | "%" | "/?" | "%?" | "*%" ) UnaryExpr }
UnaryExpr           ::= ( "-" | "!" | "~" | "typeof" ) UnaryExpr | PostfixExpr

PostfixExpr         ::= PrimaryExpr { MemberAccess | TupleIndex | SafeNav | SafeIndex | GenericInvoke | CallExpr | IndexExpr | SliceExpr | PostfixTry }
GenericInvoke       ::= "::" GenericApplication
MemberAccess        ::= "." Identifier
TupleIndex          ::= "." DecimalIndex
SafeNav             ::= "?." Identifier
SafeIndex           ::= "?[" Expression "]"
IndexExpr           ::= "[" Expression "]"
SliceRange          ::= [ BitOrExpr ] ".." [ BitOrExpr ] | [ BitOrExpr ] "..=" BitOrExpr
SliceExpr           ::= "[" SliceRange "]"

Argument            ::= [ Identifier ":" ] ( "mut" AssignTarget | Expression ) | "..." Expression
Arguments           ::= Argument { "," Argument } [ "," ]
ArgumentsCall       ::= "(" [ Arguments ] ")"
CallExpr            ::= ArgumentsCall [ LambdaExpr ] | LambdaExpr

MapperPrimary       ::= QualifiedName | Literal | RecordLiteral | "(" Expression ")"
MapperExpr          ::= MapperPrimary { MemberAccess | TupleIndex | IndexExpr | SliceExpr | GenericInvoke | ArgumentsCall }
ErrorMapper         ::= LambdaExpr | MapperExpr
PostfixTry          ::= "?" [ ErrorMapper ] (* ErrorMapper must appear on the same line as '?' without an intervening newline *)

PrimaryExpr         ::= Literal | InstantiatedMember | QualifiedName | UniverseValue
                      | ArrayLiteral | RecordLiteral | TupleLiteral
                      | LambdaExpr | AccessorExpr | IfExpr | MatchExpr | TypeMatch | RewriteExpr
                      | LoopExpr | WhileExpr | ForExpr | ReturnExpr | BreakExpr | ContinueExpr
                      | ResumeExpr | WithExpr | Block | "(" Expression ")"

UniverseValue       ::= "Type" [ GenericApplication ]
Literal             ::= IntegerLiteral | FloatLiteral | ByteLiteral | ByteStringLiteral
                      | StringLiteral | RawStringLiteral | RegexLiteral | "true" | "false"

TupleLiteral        ::= "(" Expression "," [ Expression { "," Expression } [ "," ] ] ")" | "(" ")"
ArrayElement        ::= [ "..." ] Expression
ArrayLiteral        ::= "[" [ ArrayElement { "," ArrayElement } [ "," ] ] "]"

RecordField         ::= Identifier ":" Expression | Identifier
MapEntry            ::= StringLiteral ":" Expression | "[" Expression "]" ":" Expression
RecordOrMapEntry    ::= "..." Expression | RecordField | MapEntry
RecordLiteral       ::= [ TypeReference ] ".{" [ RecordOrMapEntry { "," RecordOrMapEntry } [ "," ] ] "}"

LambdaHead          ::= "\" [ ParameterList ] "->"
LambdaExpr          ::= LambdaHead InlineLambdaBody
InlineLambdaBody    ::= LogicalOrExpr | AssignTarget AssignmentOp LogicalOrExpr
AccessorExpr        ::= "\" "." Identifier { "." Identifier }

RewriteExpr         ::= "rewrite" ( QualifiedName | "(" Expression ")" ) "in" Expression
IfExpr              ::= "if" ( "let" Pattern "=" Expression [ "if" Expression ] | Expression ) Block [ "else" ( IfExpr | Block ) ]
WhileExpr           ::= "while" ( "let" Pattern "=" Expression [ "if" Expression ] | Expression ) Block
ForBindings         ::= "as" Pattern [ "," Pattern ]
ForExpr             ::= "for" Expression ForBindings Block
LoopExpr            ::= "loop" Block
ReturnExpr          ::= "return" [ Expression ]
BreakExpr           ::= "break" [ Expression ]
ContinueExpr        ::= "continue"
ResumeExpr          ::= "resume" "(" Expression ")"
```
