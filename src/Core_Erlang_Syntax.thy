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

datatype bitstring_pattern = BitstringPattern  annotated_pattern "expression list"

datatype annotated_module = AnnotatedModule module |  AnnotatedModuleWithConst module "const list"

datatype annotated_variable = AnnotatedVar variable_name | AnnotatedVarWithConst variable_name "const list"




section ‹Static Semantics›

subsection  ‹Module Definition›

(** Validate Exported Functions **)

fun get_fun_name :: "function_definition ⇒ function_name" where
"get_fun_name (FunctionDefinition  (AnnotatedFunctionName function_name _) _) = function_name" 

fun validate_exports :: "module ⇒ bool" where
"validate_exports (Module _ (ModuleHeader exports _) (ModuleBody fun_defs) _) =
  (∀fun_name ∈ set(map (λ (Export fname)=> fname ) exports).
   ∃def_fname ∈ set (map (λ(FunctionDefinition (AnnotatedFunctionName fname _) _) => fname) fun_defs).
  def_fname = fun_name)"



(** Validate Module Attributes **)
fun get_key :: "attribute ⇒ atom" where
"get_key (Attribute key _) = key"

fun is_distinct :: "'a list ⇒ bool" where
"is_distinct [] = True" |
"is_distinct (xx#xs) = (xx ∉ set xs ∧ is_distinct xs)"

fun validate_unique_attributes :: "module ⇒ bool" where
"validate_unique_attributes (Module _ (ModuleHeader _ attrs) _ _) =
  distinct (map get_key attrs)"


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


fun get_arity :: "function_definition ⇒ integer" where
"get_arity (FunctionDefinition  (AnnotatedFunctionName (FunctionName  _  arity) _) _)  = arity"

fun get_fun_params :: "function_definition ⇒ annotated_variable_name list" where
"get_fun_params (FunctionDefinition  _ (AnnotatedFun (Func params _) _))  = params"

fun validate_function_definitions :: "module ⇒ bool" where
"validate_function_definitions (Module _ _ (ModuleBody fun_defs) _) =
  (∀fun_def ∈ set fun_defs.  (integer_to_nat (get_arity fun_def)) =  ((length (get_fun_params fun_def)):: nat))"
  
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

subsection  ‹Expressions›
(* Function name & Variable name scope binding*)

datatype scope = Scope "variable_name list" "function_name list"

fun extract_function_name :: "function_definition ⇒ function_name" where
"extract_function_name (FunctionDefinition (AnnotatedFunctionName fname _) _) = fname"

fun extract_var_name :: "annotated_variable_name ⇒ variable_name" where
"extract_var_name (AnnotatedVarName var_name) = var_name"|
"extract_var_name (AnnotatedVarNameWithConst var_name _) = var_name"

fun extract_var_name_list :: "variables ⇒ variable_name list" where
"extract_var_name_list (Variables (AnnotatedVarName var_name)) = [var_name]"|
"extract_var_name_list  (Variables (AnnotatedVarNameWithConst var_name _)) = [var_name]" |
"extract_var_name_list (VariablesList vars) = map extract_var_name vars "

fun add_var_to_scope :: "variable_name ⇒ scope ⇒ scope" where
"add_var_to_scope var (Scope vars funcs) = Scope (var # vars) funcs"

fun add_vars_to_scope :: "variable_name list ⇒ scope ⇒ scope" where
"add_vars_to_scope [] scope = scope" |
"add_vars_to_scope (var # vs) scope = add_vars_to_scope vs (add_var_to_scope var scope)"

fun add_func_to_scope :: "function_name ⇒ scope ⇒ scope" where
"add_func_to_scope func (Scope vars funcs) = Scope vars (func # funcs)"

fun in_scope_var :: "variable_name ⇒ scope ⇒ bool" where
"in_scope_var var (Scope vars _) = (var ∈ set vars)"

fun in_scope_func :: "function_name ⇒ scope ⇒ bool" where
"in_scope_func func (Scope _ funcs) = (func ∈ set funcs)"

fun extract_def_body :: "function_definition ⇒ expression" where
"extract_def_body (FunctionDefinition _ (AnnotatedFun (Func _ body) _))  =  body"

fun extract_def_vars :: "function_definition ⇒ annotated_variable_name list" where
"extract_def_vars (FunctionDefinition _ (AnnotatedFun (Func vars _) _))  =  vars"

fun validate_expr :: "expression ⇒ scope ⇒ bool" where
"validate_expr (SingleExp (VarNameExpr var) None) scope = in_scope_var var scope" |
"validate_expr (SingleExp (FuncNameExpr func)None) scope = in_scope_func func scope" |
"validate_expr (SingleExp (LetExpr (ErlangLet  vars e1 e2)) None) scope =
  (validate_expr e1 scope ∧ validate_expr e2 (add_vars_to_scope (extract_var_name_list vars) scope))" |
"validate_expr (SingleExp (FunExpr (Func vars body)) None) scope =
  validate_expr body (add_vars_to_scope (map extract_var_name vars) scope)" |
"validate_expr (SingleExp (TryExpr  e1  vars1 e2  vars2 e3) None) scope =
  (validate_expr e1 scope ∧ validate_expr e2 (add_vars_to_scope (extract_var_name_list vars1) scope) ∧
   validate_expr e3 (add_vars_to_scope (extract_var_name_list vars2) scope))" |
"validate_expr (SingleExp (LetRecExpr defs exp) None) scope =
  (let new_scope = foldr add_func_to_scope (map extract_function_name defs) scope in
  (∀def ∈ set defs. validate_expr (extract_def_body def) (add_vars_to_scope (map extract_var_name (extract_def_vars def)) new_scope))
   ∧ validate_expr exp new_scope)" |
"validate_expr _ _ = True"




(*To be checked: validating only function expressions. Not definitions*)
fun validate_fun :: "expression ⇒ bool" where
"validate_fun (SingleExp (FunExpr (Func vars _)) None) = distinct vars" |
"validate_fun _ = True"


fun validate_let :: "expression ⇒ bool" where
"validate_let (SingleExp (LetExpr (ErlangLet (VariablesList vars) _ _)) None) =  distinct vars" |
"validate_let _ = True"


(*To be checked: validating only TryExpr inside single expression*)
fun validate_try :: "expression ⇒ bool" where
"validate_try (SingleExp (TryExpr  _ (VariablesList vars1) _ (VariablesList vars2) _) None ) =  ((distinct vars1) ∨ (distinct vars2))" |
"validate_try _ = True"

(*To be checked: validating only catchExpr inside single expression*)
(*catch has no variable?? not even a list of expressions*)
(*fun validate_catch :: "expression ⇒ bool" where
"validate_catch (SingleExp (CatchExpr exps) None ) =  distinct exps " |
"validate_catch _ = True"
*)

fun get_patterns_list :: "annotated_clause  ⇒ pattern list" where 
"get_patterns_list (Clause (PatternsList patts) _ _ _ ) = patts" |
"get_patterns_list (Clause (Patterns patt) _ _ _ ) = [patt]"

fun validate_case :: "expression ⇒ bool" where
"validate_case (SingleExp (CaseExpr (ErlangCase _ clauses)) None) =   (∀c1 ∈ set clauses. ∀c2 ∈ set clauses. length (get_patterns_list c1) = length (get_patterns_list c2))" |
"validate_case _ = True"

(*To be checked: validating only receive inside single expression*)
fun validate_receive :: "expression ⇒ bool" where
"validate_receive (SingleExp (ReceiveExpr clauses _ _) None) = (∀c ∈ set clauses. length (get_patterns_list c) = 1)" |
"validate_receive _ = True"


fun get_function_names :: "function_definition list ⇒ annotated_function_name list" where
"get_function_names [] = []" |
"get_function_names ((FunctionDefinition fname _) # defs) =  fname # get_function_names defs"

fun validate_letrec :: "expression ⇒ bool" where
"validate_letrec (SingleExp(LetRecExpr defs _) None) = distinct (get_function_names defs)" |
"validate_letrec _ = True"

(*Clause and Patterns*)
fun extract_vars_from_annotated_pattern :: "annotated_pattern ⇒ variable_name" where
"extract_vars_from_annotated_pattern (AnnotatedPatern pat) = undefined"|
"extract_vars_from_annotated_pattern (AnnotatedPaternWithConst _ _) = undefined"|
"extract_vars_from_annotated_pattern (AnnotatedVarPattern var) = extract_var_name var"

fun extract_vars_from_pattern :: "pattern ⇒ variable_name list" where
"extract_vars_from_pattern (AtomicLitPat _) = []" |
"extract_vars_from_pattern (TuplePat patts) = map extract_vars_from_annotated_pattern patts" |
"extract_vars_from_pattern (ListPat patts) = map extract_vars_from_annotated_pattern patts " |
"extract_vars_from_pattern (BitstringPat patts) = map extract_vars_from_annotated_pattern patts" |
"extract_vars_from_pattern (ListPatWithTail patts patt) =extract_vars_from_pattern patt @ (map extract_vars_from_annotated_pattern patts)"

fun is_valid_clause_pattern :: "annotated_clause ⇒ bool " where
"is_valid_clause_pattern (Clause ( Patterns patt) _ _ _) = distinct (extract_vars_from_pattern patt) "|
"is_valid_clause_pattern (Clause ( PatternsList patts) _ _ _) = distinct (map extract_vars_from_pattern patts) "

fun valid_annotated_pattern :: "annotated_pattern ⇒ bool" where
"valid_annotated_pattern  (AnnotatedVarPattern var_name) = True" |
"valid_annotated_pattern  (AnnotatedPatern (AtomicLitPat atom)) = True" |
"valid_annotated_pattern _ = False"

fun valid_expression :: "expression ⇒ bool" where
"valid_expression (SingleExp (AtomicLitExpr _) None) = True" |
"valid_expression  (SingleExp (VarNameExpr _)None) = True" |
"valid_expression _ = False"


fun is_valid_bitstring_pattern :: "bitstring_pattern ⇒ bool" where
"is_valid_bitstring_pattern (BitstringPattern patt exps) = 
  (valid_annotated_pattern patt ∧ (∀exp ∈ set(map valid_expression exps). exp))"

fun is_valid_guard :: "expression ⇒ bool" where
"is_valid_guard (SingleExp (ReceiveExpr _ _ _) _) = False" |
"is_valid_guard (SingleExp (AppExpr _ _) _) = False" |
(*"is_valid_guard (SingleExp (TryExpr (ETry e1 vars e2 catch_vars e3))_) = 
   ((vars = e2) ∧ (catch_vars = e3) ∧ (e3 = AtomicLitExpr (ConstAtom (AtomLiteral (Atom [''false''])))))" |*)
"is_valid_guard _ = True"

fun validate_clause :: "annotated_clause ⇒ bool" where
"validate_clause (Clause ps (When guard) body annotation) = 
  ((is_valid_clause_pattern((Clause ps (When guard) body annotation )) ∧ is_valid_guard guard ∧ valid_expression body))"


(**)


end