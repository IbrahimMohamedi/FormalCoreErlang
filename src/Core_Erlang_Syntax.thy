theory Core_Erlang_Syntax
  imports Main
begin



(*Core Erlang Lexical Definitions*)


datatype sign = Plus | Minus

datatype digit = Zero | One | Two | Three | Four | Five | Six | Seven | Eight | Nine

datatype uppercase = A | B | C | D | E | F | G | H | I | J | K | L | M | 
                     N | O | P | Q | R | S | T | U | V | W | X | Y | Z | 
                     u00c0 | u00c1 | u00c2 | u00c3 | u00c4 | u00c5 | 
                     u00c6 | u00c7 | u00c8 | u00c9 | u00ca | u00cb | 
                     u00cc | u00cd | u00ce | u00cf | u00d0 | u00d1 | 
                     u00d2 | u00d3 | u00d4 | u00d5 | u00d6 | u00d8 | 
                     u00d9 | u00da | u00db | u00dc | u00dd | u00de

datatype lowercase = a | b | c | d | e | f | g | h | i | j | k | l | m | 
                     n | o | p | q | r | s | t | u | v | w | x | y | z | 
                     u00df | u00e0 | u00e1 | u00e2 | u00e3 | u00e4 | 
                     u00e5 | u00e6 | u00e7 | u00e8 | u00e9 | u00ea | 
                     u00eb | u00ec | u00ed | u00ee | u00ef | u00f0 | 
                     u00f1 | u00f2 | u00f3 | u00f4 | u00f5 | u00f6 | 
                     u00f8 | u00f9 | u00fa | u00fb | u00fc | u00fd | 
					           u00fe | u00ff


definition valid_inputchar :: "char \<Rightarrow> bool"
  where
    "valid_inputchar ch \<equiv>
     (\<not> ch =  CHR 0x0A)  \<and> 
     (\<not>  ch =  CHR 0x0D) "

datatype inputchar = InputChar char


datatype control = u0000 | u0001 | u0002 | u0003 | u0004 | u0005 | u0006 | u0007 | u0008 | u0009 | u000a | 
                   u000b | u000c | u000d | u000e | u000f | u0010 | u0011 | u0012 | u0013 | u0014 | u0015 | 
				            u0016 | u0017 | u0018 | u0019 | u001a | u001b | u001c | u001d | u001e | u001f

datatype space = u0020 
datatype backslash = u005d
datatype singleqoute = u0027
datatype doubleqoute = u0022
datatype dolar = u0024
datatype caret = u005e
datatype hash = u0023

datatype namechar = Uppercase uppercase | Lowercase lowercase | Digit digit | At | Underscore 

datatype octaldigit = zero | one | two | three | four | five | six | seven

datatype  octal = OctalDigit octaldigit "octaldigit  option" "octaldigit  option"


datatype ctrlchar = u0040 | u0041 | u0042 | u0043 | u0044 | u0045 | u0046 | 
                    u0047 | u0048 | u0049 | u004a | u004b | u004c | u004d | 
                    u004e | u004f | u0050 | u0051 | u0052 | u0053 | u0054 | 
                    u0055 | u0056 | u0057 | u0058 | u0059 | u005a | u005b | 
                    u005c | u005d | u005e | u005f

datatype escapechar = B | D | E | F | N | R | S | T | V | BackSlash | SingleQuote | DoubleQuote

datatype escape =  EscapeOctal  octal | EscapeCtrlChar  ctrlchar | EscapeChar  escapechar



(*Xore Erlang Terminals*)
datatype 'a nonemptylist = Nonemptylist 'a "'a list"

datatype integer = Integer "sign option" "digit nonemptylist"

value "Integer None (Nonemptylist Eight [])"

datatype exponent_part = Exponent_part   "sign option" "digit nonemptylist"

datatype float = Float  "sign option" "digit nonemptylist "  "digit nonemptylist " "exponent_part option"

datatype atom = Atom  "inputchar list" | EscapeAtom "escape list"

datatype erlang_char = Char  inputchar | Escapechar  escape

datatype erlang_string = String  "erlang_char list"


datatype variable_name = UpperCharVar uppercase "namechar list"| UnderScoreVar "namechar nonemptylist"




(*Core Erlang Non-Terminals*)



datatype nil = Nil

  datatype atomic_literal = IntegerLiteral integer
                    | FloatLiteral float
                    | AtomLiteral  atom
                    | NilLiteral  nil
                    | CharLiteral  erlang_char
                    | StringLiteral erlang_string

datatype function_name = FunctionName  atom  integer

datatype function_definition = FunctionDefinition  annotated_function_name  annotated_fun

and annotated_function_name = FunctionName function_name | AnnotatedFunctionName function_name "const list"

and annotated_fun = Function func | AnnotatedFun  func " const list"

and  variables = Variables annotated_variable_name
            | VariablesList "annotated_variable_name list"

and annotated_variable_name = AnnotatedVarName variable_name | AnnotatedVarNameWithConst variable_name " const list"

and  const = ConstAtom  atomic_literal |ConstList "const nonemptylist" |ConstTuple const tuple | ConstListWithTail "const nonemptylist" const

and annotated_pattern = AnnotatedVarPattern annotated_variable_name | AnnotatedPatern pattern |  AnnotatedPaternWithConst pattern "const list"

and pattern = AtomicLitPat atomic_literal
             | TuplePat "annotated_pattern list"
             | ListPat "annotated_pattern list"
             | BitstringPat  "annotated_pattern list" 
             |  ListPatWithTail "annotated_pattern list" pattern


and expression = ValueListExp annotated_value_list| SingleExp annotated_single_expression

and annotated_value_list =  AnnValueList value_list | AnnotatedValueList value_list "const list"

and annotated_single_expression = AnnotatedExpr single_expression
                                  | AnnotatedExprWithConstants single_expression "const list"

and single_expression = AtomicLitExpr atomic_literal
                      | VarNameExpr variable_name
                      | FuncNameExpr function_name
                      | TupleExpr tuple
                      | ListExpr expr_list
                      | BinaryExp binary
                      | LetExpr Let
                      | CaseExpr Case
                      | FunExpr func
                      | LetRecExpr letrec
                      | AppExpr application
                      | InterModuleCallExpr inter_module_call
                      | PrimOpCallExpr prim_op_call
                      | TryExpr Try
                      | ReceiveExpr receive
                      | SequencingExpr sequencing
                      | CatchExpr catch
and value_list = ValueList "annotated_single_expression list"

and tuple = Tuple "expression list"

and expr_list = List "expression nonemptylist"
         | ListWithTail "expression nonemptylist" expression
and binary = Binary  "bit_string list" 

and bit_string = BitString  expression "expression list" 

and Let = LetE variables expression expression

and Case = ECase expression "annotated_clause list"

and annotated_clause = AnnotatedClause clause
                      | AnnotatedClauseWithConstants clause "const list"

and clause = Clause patterns guard expression

and patterns = Patterns pattern | PatternsList "pattern list"

and guard = When expression

and func = Fun "annotated_variable_name list" expression

and letrec = Letrec "function_definition list" expression

and application = Apply expression "expression list"

and inter_module_call = call  expression expression  "expression list"

and prim_op_call = primop string atom  "expression list"

and Try = ETry expression variables expression variables expression

and receive = Receive "annotated_clause list" timeout

and timeout = Timeout expression expression 

and sequencing = Sequencing expression expression

and catch = Catch expression

(*                      ----------------------------------------                  *)


datatype bitstring_pattern = BitstringPatern  annotated_pattern "expression list"

datatype annotated_module = AModule module  | AnnotatedModule  module  "const list"

datatype annotated_variable = AnnotatedVar variable_name | AnnotatedVarWithConst variable_name "const list"

datatype  annotation = Annotation "const list"

datatype  module_end = End

datatype module_body = ModuleBody "function_definition list"

datatype  attribute = Attribute  atom  const

datatype  export = Export  function_name

datatype  module_header = ModuleHeader "export list"  "attribute list"

datatype  module_header = ModuleHeader "export list"  "attribute list"

datatype module = Module  atom module_header module_body module_end

datatype module_header = ModuleHeader "export list"  "attribute list"

datatype annotated_module = AnnotatedModule module |  AnnotatedModuleWithConst module "const list"


(*
and function_definition = FunctionDefinition  annotated_function_name  annotated_fun



and annotation = Annotation "const list"



and

and module_end = End


and annotated_pattern = AnnotatedVariable annotated_variable
                        | AnnotatedPat pattern
                        | AnnotatedPattern pattern "const list" 

and annotated_variable = AnnotatedVar variable_name | AnnotatedVarWithConst variable_name "const list"

*)




















(*needs to be checked:
Constant (c):
AtomicLiteral
{ c1 , . . . , cn } (n  0)
[ c1 , . . . , cn ] (n  1)
[ c1 , . . . , cn−1 | cn ] (n  2)*)


(* what is v
AnnotatedPattern (p):
v1
Pattern
( Pattern -| [ c1 , . . . , cn ] ) (n  0)*)




end
