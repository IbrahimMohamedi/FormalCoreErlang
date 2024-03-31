theory Core_Erlang_Syntax
  imports Main
begin

section ‹Syntax›

subsection ‹Core Erlang Lexical Definitions›

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

datatype inputchar = InputChar char

definition valid_inputchar :: "char ⇒ bool"
  where
    "valid_inputchar ch ≡
     (¬ ch =  CHR 0x0A)  ∧
     (¬  ch =  CHR 0x0D) "

datatype control = u0000 | u0001 | u0002 | u0003 | u0004 | u0005 | u0006 | u0007 | u0008 | u0009 | u000a |
                   u000b | u000c | u000d | u000e | u000f | u0010 | u0011 | u0012 | u0013 | u0014 | u0015 |
                   u0016 | u0017 | u0018 | u0019 | u001a | u001b | u001c | u001d | u001e | u001f

datatype space = u0020
datatype backslash = u005d
datatype singleqoute = u0027
datatype doubleqoute = u0022
datatype dollar = u0024
datatype caret = u005e
datatype hash = u0023

datatype namechar = Uppercase uppercase | Lowercase lowercase | Digit digit | At | Underscore

datatype octaldigit = OctalZero | OctalOne | OctalTwo | OctalThree | OctalFour | OctalFive | OctalSix | OctalSeven

datatype octal = OctalDigit octaldigit "octaldigit option" "octaldigit option"

datatype ctrlchar = u0040 | u0041 | u0042 | u0043 | u0044 | u0045 | u0046 |
                    u0047 | u0048 | u0049 | u004a | u004b | u004c | u004d |
                    u004e | u004f | u0050 | u0051 | u0052 | u0053 | u0054 |
                    u0055 | u0056 | u0057 | u0058 | u0059 | u005a | u005b |
                    u005c | u005d | u005e | u005f

datatype escapechar = B | D | E | F | N | R | S | T | V | BackSlash | SingleQuote | DoubleQuote

datatype escape =  EscapeOctal octal | EscapeCtrlChar ctrlchar | EscapeChar escapechar

subsection ‹Core Erlang Terminals›

datatype 'a nonemptylist = Nonemptylist 'a "'a list"

datatype integer = Integer "sign option" "digit nonemptylist"

datatype exponent_part = Exponent_part "sign option" "digit nonemptylist"

datatype float = Float "sign option" "digit nonemptylist" "digit nonemptylist" "exponent_part option"

datatype atom = Atom "inputchar list" | EscapeAtom "escape list"

datatype erlang_char = Char inputchar | Escapechar escape

datatype erlang_string = String "erlang_char list"

datatype variable_name = UpperCharVar uppercase "namechar list" | UnderscoreVar "namechar nonemptylist"

subsection ‹Core Erlang Non-Terminals›

datatype erlang_nil = ErlangNil

datatype atomic_literal = IntegerLiteral integer
  | FloatLiteral float
  | AtomLiteral atom
  | NilLiteral erlang_nil
  | CharLiteral  erlang_char
  | StringLiteral erlang_string
datatype  const = ConstAtom  atomic_literal |ConstList "const nonemptylist" |ConstTuple "const list" | ConstListWithTail "const nonemptylist" const

datatype  annotation = Annotation "const list"

datatype annotated_variable_name = AnnotatedVarName variable_name | AnnotatedVarNameWithConst variable_name " const list"


datatype  variables = Variables annotated_variable_name
            | VariablesList "annotated_variable_name list"


datatype function_name = FunctionName  atom  integer


datatype annotated_pattern = AnnotatedVarPattern annotated_variable_name | AnnotatedPatern pattern |  AnnotatedPaternWithConst pattern "const list"
and pattern = AtomicLitPat atomic_literal
             | TuplePat "annotated_pattern list"
             | ListPat "annotated_pattern list"
             | BitstringPat  "annotated_pattern list" 
             |  ListPatWithTail "annotated_pattern list" pattern


datatype patterns = Patterns pattern | PatternsList "pattern list"

(*To be checked*)
datatype annotated_function_name = AnnotatedFunctionName function_name "annotation option" 

datatype 'a annotated = Annotated 'a "const list" | Unannotated 'a



datatype annotated_fun = AnnotatedFun func "annotation option"

and function_definition = FunctionDefinition  annotated_function_name annotated_fun

and func = Func "annotated_variable_name list" expression


and expression = ValueListExp "value_list annotated"| SingleExp single_expression  "annotation option"


and single_expression = AtomicLitExpr atomic_literal
                      | VarNameExpr variable_name
                      | FuncNameExpr function_name
                      | TupleExpr tuple
                      | ListExpr erlang_list
                      | BinaryExp   "bit_string list"
                      | LetExpr erlang_let
                      | CaseExpr erlang_case
                      | FunExpr func
                      | LetRecExpr "function_definition list" expression
                      | AppExpr  expression "expression list"
                      | InterModuleCallExpr  expression expression  "expression list"
                      | PrimOpCallExpr  string atom  "expression list"
                      | TryExpr  expression variables expression variables expression
                      | ReceiveExpr  "annotated_clause list" expression expression
                      | SequencingExpr expression expression
                      | CatchExpr expression

and value_list = ValueList " single_expression annotated list"


and tuple = Tuple "expression list"

and erlang_list = List "expression nonemptylist"
				| ListWithTail "expression nonemptylist" expression


and bit_string = BitString  expression "expression list" 

and erlang_let = ErlangLet variables expression expression

and erlang_case = ErlangCase expression "annotated_clause list"

and annotated_clause = Clause patterns guard expression  "annotation list"


and guard = When expression



datatype letrec = Letrec "function_definition list" expression

datatype application = Apply expression "expression list"

datatype inter_module_call = call  expression expression  "expression list"

datatype prim_op_call = primop string atom  "expression list"

datatype Try = ETry expression variables expression variables expression

datatype timeout = Timeout expression expression

datatype receive = Receive "annotated_clause list" timeout

datatype sequencing = Sequencing expression expression

datatype catch = Catch expression




(*                      ----------------------------------------                  *)

datatype  module_end = End

datatype  attribute = Attribute  atom  const

datatype  export = Export  function_name

datatype  module_header = ModuleHeader "export list"  "attribute list"

datatype module_body = ModuleBody "function_definition list"

datatype module = Module  atom module_header module_body module_end

datatype bitstring_pattern = BitstringPatern  annotated_pattern "expression list"

datatype annotated_module = AnnotatedModule module |  AnnotatedModuleWithConst module "const list"

datatype annotated_variable = AnnotatedVar variable_name | AnnotatedVarWithConst variable_name "const list"




section ‹Static Semantics›

subsection  ‹Module Definition›

(** Validate Exported Functions **)

fun extract_fun_name :: "function_definition ⇒ function_name" where
"extract_fun_name (FunctionDefinition  (AnnotatedFunctionName function_name _) _) = function_name" 

fun validate_exports :: "module ⇒ bool" where
"validate_exports (Module _ (ModuleHeader exports _) (ModuleBody fun_defs) _) =
  (∀fun_name ∈ set(map (λ (Export fname)=> fname ) exports).
   ∃def_fname ∈ set (map (λ(FunctionDefinition (AnnotatedFunctionName fname _) _) => fname) fun_defs).
  def_fname = fun_name)"



(** Validate Module Attributes **)
fun extract_key :: "attribute ⇒ atom" where
"extract_key (Attribute key _) = key"

fun is_distinct :: "'a list ⇒ bool" where
"is_distinct [] = True" |
"is_distinct (xx#xs) = (xx ∉ set xs ∧ is_distinct xs)"

fun validate_unique_attributes :: "module ⇒ bool" where
"validate_unique_attributes (Module _ (ModuleHeader _ attrs) _ _) =
  distinct (map extract_key attrs)"


(** Validate Function parameters **)

fun digit_to_nat :: "digit ⇒ nat" where
  "digit_to_nat Zero = 0"
| "digit_to_nat One = 1"
| "digit_to_nat Two = 2"
| "digit_to_nat Three = 3"
| "digit_to_nat Four = 4"
| "digit_to_nat Five = 5"
| "digit_to_nat Six = 6"
| "digit_to_nat Seven = 7"
| "digit_to_nat Eight = 8"
| "digit_to_nat Nine = 9"

fun nonemptylist_to_nat :: "digit nonemptylist ⇒ nat" where
  "nonemptylist_to_nat (Nonemptylist num []) = digit_to_nat num"
| "nonemptylist_to_nat (Nonemptylist num ds) = digit_to_nat num * 10 + nonemptylist_to_nat (Nonemptylist (hd ds) (tl ds))"

fun integer_to_nat :: "integer ⇒ nat" where
  "integer_to_nat (Integer (Some Plus) ds) = nonemptylist_to_nat ds"
| "integer_to_nat (Integer (Some Minus) ds) =  nonemptylist_to_nat ds"
| "integer_to_nat (Integer None ds) = nonemptylist_to_nat ds"


fun extract_arity :: "function_definition ⇒ integer" where
"extract_arity (FunctionDefinition  (AnnotatedFunctionName (FunctionName  _  arity) _) _)  = arity"

fun extract_fun_params :: "function_definition ⇒ annotated_variable_name list" where
"extract_fun_params (FunctionDefinition  _ (AnnotatedFun (Func params _) _))  = params"

fun validate_function_definitions :: "module ⇒ bool" where
"validate_function_definitions (Module _ _ (ModuleBody fun_defs) _) =
  (∀fun_def ∈ set fun_defs.  (integer_to_nat (extract_arity fun_def)) =  ((length (extract_fun_params fun_def)):: nat))"
  
(** Validate Unique Function Names  **)

fun validate_unique_function_names :: "module ⇒ bool" where
"validate_unique_function_names (Module _ _ (ModuleBody fun_defs) _) =
  distinct (map (λ(FunctionDefinition (AnnotatedFunctionName fname _) _) => fname) fun_defs)"

subsection  ‹Atomic literals›

(*To be checked: Empty Strings ""*)
fun erlang_string_to_erlang_list :: "erlang_string ⇒ erlang_list" where
"erlang_string_to_erlang_list (String chars) = List (Nonemptylist ( SingleExp (AtomicLitExpr (CharLiteral( Char (InputChar CHR 0x020)))) None) (map (λchar. SingleExp (AtomicLitExpr (CharLiteral char)) None) chars) )"

subsection  ‹Lists›

fun list_to_normal_form :: "erlang_list ⇒ erlang_list" where
  "list_to_normal_form (List exps) = ListWithTail exps (SingleExp (AtomicLitExpr (NilLiteral(ErlangNil))) None) " |
  "list_to_normal_form (ListWithTail exps exp) = ListWithTail exps exp"

fun list_to_nonemptylist :: "'a list ⇒ 'a nonemptylist" where
 " list_to_nonemptylist [] = undefined"|
  " list_to_nonemptylist (exp_x#exp_xs) = Nonemptylist exp_x exp_xs"

fun list_with_tail_to_normal_form :: "erlang_list ⇒ erlang_list" where
 "list_with_tail_to_normal_form (List xs ) = undefined" |
 "list_with_tail_to_normal_form (ListWithTail (Nonemptylist x_head []) x_tail) = ListWithTail (Nonemptylist x_head []) x_tail" |
  "list_with_tail_to_normal_form (ListWithTail (Nonemptylist x_head (y_head # ys)) x_tail) = 
    ListWithTail (Nonemptylist x_head (y_head#(butlast ys))) (SingleExp (ListExpr (ListWithTail (Nonemptylist (last ys) []) x_tail)) None)"
(*
fun list_with_tail_to_normal_form_2 :: "erlang_list ⇒ erlang_list" where
  "list_with_tail_to_normal_form_2 (ListWithTail (Nonemptylist exp_x []) ys) = ListWithTail (Nonemptylist exp_x []) ys" |
  "list_with_tail_to_normal_form_2 (ListWithTail (Nonemptylist exp_x (exp_xs)) ys) = 
     ListWithTail (Nonemptylist exp_x []) (list_with_tail_to_normal_form (ListWithTail (list_to_nonemptylist exp_xs) ys))"
*)


(*
fun list_with_tail_to_normal_form :: "erlang_list ⇒ erlang_list" where
  "list_with_tail_to_normal_form (ListWithTail exps exp) = 
     (if length exps > 1 
      then ListWithTail (butlast exps) (ListWithTail [last exps] exp) 
      else ListWithTail exps exp)"
*)

(*fun square::" nat ⇒ nat" where
"square num = num * num"

value "map square [1,2,3]"

value "(map (extract_fun_name fun_defs))"
*)

(**)


end