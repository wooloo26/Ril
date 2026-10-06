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
(* 2. Types, Static Sorts, and Type Computation                              *)
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

TypeExpression      ::= FunctionType | TypeClosureSort | UnionType
UnionType           ::= PrefixType { "|" PrefixType }
PrefixType          ::= "?" PrefixType | "[" "]" PrefixType | "keyof" PrefixType | PostfixType
PostfixType         ::= PrimaryType { "[" Expression "]" }
PrimaryType         ::= PrimitiveType | StaticSortReference | TypeReference | RecordType | TupleType | LiteralType
                      | "_" | "(" TypeExpression ")" | "typeof" Expression | StaticCall

PrimitiveType       ::= "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
                      | "int" | "bigint" | "f32" | "f64" | "bool" | "str" | "bytes" | "never"

TypeMatch           ::= "match" "type" TypeExpression "{" TypeMatchArm { "," TypeMatchArm } [ "," ] "}"
TypeMatchArm        ::= TypePattern "->" Expression
TypePattern         ::= "infer" Identifier | "_" | "never" | LiteralType | TypePatternRef
                      | "?" TypePattern | "[" "]" TypePattern
                      | TupleTypePattern
                      | "(" ")" | RecordTypePattern | FunctionTypePattern
TypePatternRef      ::= QualifiedName [ "<" TypePattern { "," TypePattern } [ "," ] ">" ]
RecordTypePattern   ::= "{" [ PatternTypeField { "," PatternTypeField } [ "," ] ] "}"
PatternTypeField    ::= [ "mut" ] Identifier ":" TypePattern
PatternCallableParam::= [ "mut" ] TypePattern
FunctionTypePattern ::= [ "halt" ] "fn" "(" [ PatternCallableParam { "," PatternCallableParam } [ "," ] ] ")"
                        "->" TypePattern { ContractArgument }

TupleType           ::= "(" ")" | "(" TupleTypeEntry "," [ TupleTypeEntries ] ")"
TupleTypeEntries    ::= TupleTypeEntry { "," TupleTypeEntry } [ "," ]
TupleTypeEntry      ::= [ "..." ] TypeExpression
TupleTypePattern    ::= "(" ")" | "(" TupleTypeRest [ "," ] ")"
                      | "(" TypePattern "," [ TuplePatternTail ] ")"
TuplePatternTail    ::= TypePattern { "," TypePattern } [ "," TupleTypeRest ] [ "," ]
                      | TupleTypeRest [ "," ]
TupleTypeRest       ::= "..." "infer" Identifier
RecordType          ::= "{" [ RecordTypeEntry { "," RecordTypeEntry } [ "," ] ] "}"
RecordTypeEntry     ::= RecordTypeField | OpaqueTypeMember | MappedTypeField | RecordTypeSpread | RowTail
RecordTypeSpread    ::= "..." TypeExpression
RowTail             ::= ".." [ Identifier | "_" ]
RecordTypeField     ::= [ "mut" ] Identifier ":" TypeExpression [ "=" Expression ]
OpaqueTypeMember    ::= "opaque" "type" Identifier
MappedTypeField     ::= [ "mut" ] "[" Identifier "in" "keyof" TypeExpression
                        [ "if" Expression ] [ "as" Expression ] "]" ":" TypeExpression [ "=" Expression ]

CallableParamType   ::= [ "mut" ] ( Identifier ":" TypeExpression | TypeExpression )
FunctionType        ::= [ "halt" ] "fn" [ GenericParameters ] "("
                        [ CallableParamType { "," CallableParamType } [ "," ] ] ")"
                        "->" TypeExpression { ContractArgument } [ WhereClause ]

(* ========================================================================= *)
(* 3. Declarations and Items                                                 *)
(* ========================================================================= *)

Item                ::= LetDecl | FunctionDecl | TypeBindingDecl | SumTypeDecl | NominalDecl
                      | OpaqueDecl | EffectDecl | EffectAliasDecl
                      | ModuleDecl | UseDecl | TestDecl

LetModifier         ::= "scoped" | "view"
LetDecl             ::= [ "pub" ] "let" [ LetModifier ] Pattern [ ":" TypeExpression ] [ "=" Expression ] [ "else" Block ]
Parameter           ::= [ "mut" ] Identifier [ ":" TypeExpression ] [ "=" Expression ]
ParameterList       ::= Parameter { "," Parameter } [ "," ]

FunctionSignature   ::= [ "halt" ] "fn" Identifier [ GenericParameters ] "(" [ ParameterList ] ")"
                        [ "->" TypeExpression ] { ContractArgument } [ WhereClause ]
FunctionDecl        ::= [ "pub" ] FunctionSignature Block

SumTypeDecl         ::= [ "pub" ] "type" Identifier [ GenericParameters ] [ WhereClause ]
                        "{" VariantDecl { "," VariantDecl } [ "," ] "}"
VariantDecl         ::= Identifier [ GenericParameters ]
                        [ "(" VariantFields ")" | "{" StructFields "}" ] [ "->" TypeExpression ]
VariantFields       ::= VariantField { "," VariantField } [ "," ]
VariantField        ::= Identifier ":" TypeExpression | TypeExpression
StructFields        ::= StructFieldEntry { "," StructFieldEntry } [ "," ]
StructFieldEntry    ::= RecordTypeField | OpaqueTypeMember

NominalDecl         ::= [ "pub" ] "type" Identifier [ GenericParameters ] "(" VariantFields ")" [ WhereClause ]
OpaqueDecl          ::= [ "pub" ] "opaque" "type" Identifier [ GenericParameters ] [ WhereClause ] "=" TypeExpression
TypeBindingDecl     ::= [ "pub" ] [ "halt" ] "type" Identifier
                       [ GenericParameters ] [ WhereClause ] "=" TypeBindingInitializer
TypeBindingInitializer ::= TypeExpression | Expression
TypeClosureSort     ::= [ "halt" ] "type" "("
                       [ CallableParamType { "," CallableParamType } [ "," ] ] ")"
                       "->" TypeExpression
StaticSortReference ::= "Type" | "Record" | "Row"
TypeValueExpr       ::= "type" "[" TypeExpression "]"
StaticCall          ::= StaticCallee ArgumentsCall { ArgumentsCall }
StaticCallee        ::= QualifiedName | "(" Expression ")"

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

PrimaryExpr         ::= Literal | InstantiatedMember | QualifiedName | TypeValueExpr
                      | ArrayLiteral | RecordLiteral | TupleLiteral
                      | LambdaExpr | AccessorExpr | IfExpr | MatchExpr | TypeMatch
                      | LoopExpr | WhileExpr | ForExpr | ReturnExpr | BreakExpr | ContinueExpr
                      | ResumeExpr | WithExpr | Block | "(" Expression ")"

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

## Static Computation Parsing and Sort Checks

TypeBindingDecl is a common surface binding. Direct type/sort descriptions create aliases; a normal expression yielding Type creates a computed alias; a normal expression yielding a static callable creates a callable binding. Classification follows direct schema syntax and checked initializer sort; it never reinterprets an ordinary lambda body block or tuple based on a desired return type. Runtime callable/scalar-only initializers are not valid type bindings. A callable binding cannot have GenericParameters, and halt is permitted only for callable bindings.

TypeValueExpr is bracketed quotation. Static callable sorts always have a result arrow. Runtime FunctionType/FunctionDecl cannot use static sorts. Normal static calls work for names, parenthesized callable expressions and returned callable values, so chaining does not need a separate application dialect. Angle application belongs to data/schema constructors and erased constructor-kinded parameters, not direct callable bindings.

TypeMatch arms are normal static expressions; new Type values use type[...]. Its target retains type-description syntax for known schema names/static Type bindings. Ordinary if/block/let grammar handles computation; TypeIf and TypeBlock have no productions. One trailing tuple rest, whole-tuple rest and trailing rest commas are supported.

Direct lambda static bindings have item prebinding/SCC checking; other callable initializers are lexical and cannot eagerly use uninitialized/self-recursive values. Named patterns only decompose observable injective constructors, not arbitrary computed families or Immut. Stage, sort, provenance, visibility, regularity, totality and resource checks are semantic obligations, not new lambda syntax.

OpaqueTypeMember declares a compile-time abstract runtime-type witness in a record/struct variant. It has no initializer, mut modifier, generic header or runtime Type field; construction supplies a statically checked Type choice, and lexical opening preserves correlated value/operation types. This is distinct from module-level OpaqueDecl with a fixed representation. Implicit generic erasure does not permit erasing ordinary call arguments or their evaluation.
