theory Core_Erlang_Syntax
  imports Main
begin

section ‹Syntax›

subsection ‹Core Erlang Lexical Definitions›

consts BIT_SIZE::nat

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


datatype  variables = Variable annotated_variable_name
            | VariablesList "annotated_variable_name list"


datatype function_name = FunctionName  atom  integer


datatype annotated_pattern = AnnotatedVarPattern annotated_variable_name | AnnotatedPatern pattern |  AnnotatedPaternWithConst pattern "const list"
and pattern = AtomicLitPat atomic_literal
             | TuplePat "annotated_pattern list"
             | ListPat "annotated_pattern list"
             | BitstringPat  "annotated_pattern list" 
             |  ListPatWithTail "annotated_pattern list" annotated_pattern


datatype patterns = Pattern annotated_pattern | PatternsList "annotated_pattern list"

(*To be checked*)
datatype annotated_function_name = AnnotatedFunctionName function_name "annotation option" 

(*
datatype 'a annotated = Annotated 'a "const list" | Unannotated 'a
*)


datatype annotated_fun = AnnotatedFun func "annotation option"

and function_definition = FunctionDefinition  annotated_function_name annotated_fun

and func = Func "annotated_variable_name list" expression


and expression = ValueListExp value_list "annotation option"| SingleExp single_expression  "annotation option"


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

and value_list = ValueList "single_expression list" "annotation option"


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

datatype prim_op_call = Primop  atom  "expression list"

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

(*
fun is_distinct :: "'a list ⇒ bool" where
"is_distinct [] = True" |
"is_distinct (xx#xs) = (xx ∉ set xs ∧ is_distinct xs)"
*)

fun validate_unique_attributes :: "module ⇒ bool" where
"validate_unique_attributes (Module _ (ModuleHeader _ attrs) _ _) = distinct (map get_key attrs)"


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

(** Validate Module  **)

fun validate_module :: "module ⇒ bool" where
"validate_module mdl = (validate_exports mdl  ∧ validate_unique_attributes mdl 
                       ∧ validate_function_definitions mdl  ∧ validate_unique_function_names mdl) "


subsection  ‹Atomic literals›

(*To be checked: Empty Strings ""*)
fun erlang_string_to_erlang_list :: "erlang_string ⇒ erlang_list" where
"erlang_string_to_erlang_list (String (ch#chars)) = List (Nonemptylist ( SingleExp (AtomicLitExpr (CharLiteral ch)) None) (map (λchar. SingleExp (AtomicLitExpr (CharLiteral char)) None) chars) )"|
"erlang_string_to_erlang_list (String []) = undefined"

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

subsection  ‹Expressions›
(* Function name & Variable name scope binding*)

datatype scope = Scope "variable_name list" "function_name list"

abbreviation true :: atom where
  "true ≡ Atom [InputChar (CHR ''t''), InputChar (CHR ''r''), InputChar (CHR ''u''), InputChar (CHR ''e'')]"

abbreviation false :: atom where
  "false ≡ Atom [InputChar (CHR ''f''), InputChar (CHR ''a''), InputChar (CHR ''l''), InputChar (CHR ''s''), InputChar (CHR ''e'')]"


fun extract_function_name :: "function_definition ⇒ function_name" where
"extract_function_name (FunctionDefinition (AnnotatedFunctionName fname _) _) = fname"

fun extract_var_name :: "annotated_variable_name ⇒ variable_name" where
"extract_var_name (AnnotatedVarName var_name) = var_name"|
"extract_var_name (AnnotatedVarNameWithConst var_name _) = var_name"

fun extract_var_name_list :: "variables ⇒ variable_name list" where
"extract_var_name_list (Variable (AnnotatedVarName var_name)) = [var_name]"|
"extract_var_name_list  (Variable (AnnotatedVarNameWithConst var_name _)) = [var_name]" |
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

function validate_expr :: "expression ⇒ scope ⇒ bool" where
"validate_expr (SingleExp (VarNameExpr var) _) scope = in_scope_var var scope" |
"validate_expr (SingleExp (FuncNameExpr func)_) scope = in_scope_func func scope" |
"validate_expr (SingleExp (LetExpr (ErlangLet  vars e1 e2)) _) scope =
  (validate_expr e1 scope ∧ validate_expr e2 (add_vars_to_scope (extract_var_name_list vars) scope))" |
"validate_expr (SingleExp (FunExpr (Func vars body)) _) scope =
  validate_expr body (add_vars_to_scope (map extract_var_name vars) scope)" |
"validate_expr (SingleExp (TryExpr  e1  vars1 e2  vars2 e3) _) scope =
  (validate_expr e1 scope ∧ validate_expr e2 (add_vars_to_scope (extract_var_name_list vars1) scope) ∧
   validate_expr e3 (add_vars_to_scope (extract_var_name_list vars2) scope))" |
"validate_expr (SingleExp (LetRecExpr defs exp) _) scope =
  (let new_scope = foldr add_func_to_scope (map extract_function_name defs) scope in
  (∀def ∈ set defs. validate_expr (extract_def_body def) (add_vars_to_scope (map extract_var_name (extract_def_vars def)) new_scope))
   ∧ validate_expr exp new_scope)" |
"validate_expr _ _ = True"
  sorry
termination validate_expr
  sorry

(*To be checked: validating only function expressions. Not definitions*)
fun validate_fun :: "expression ⇒ bool" where
"validate_fun (SingleExp (FunExpr (Func vars _)) _) = distinct vars" |
"validate_fun _ = True"


fun validate_let :: "expression ⇒ bool" where
"validate_let (SingleExp (LetExpr (ErlangLet (VariablesList vars) _ _)) _) =  distinct vars" |
"validate_let _ = True"


(*To be checked: validating only TryExpr inside single expression*)
fun validate_try :: "expression ⇒ bool" where
"validate_try (SingleExp (TryExpr  _ (VariablesList vars1) _ (VariablesList vars2) _) _ ) =  ((distinct vars1) ∨ (distinct vars2))" |
"validate_try _ = True"

(*To be checked: validating only catchExpr inside single expression*)
(*catch has no variable?? not even a list of expressions*)
(*fun validate_catch :: "expression ⇒ bool" where
"validate_catch (SingleExp (CatchExpr exps) None ) =  distinct exps " |
"validate_catch _ = True"
*)

fun get_patterns_list :: "annotated_clause  ⇒ annotated_pattern list" where 
"get_patterns_list (Clause (PatternsList patts) _ _ _ ) = patts" |
"get_patterns_list (Clause (Pattern patt) _ _ _ ) = [patt]"

fun validate_case :: "expression ⇒ bool" where
"validate_case (SingleExp (CaseExpr (ErlangCase _ clauses)) _) =   (∀c1 ∈ set clauses. ∀c2 ∈ set clauses. length (get_patterns_list c1) = length (get_patterns_list c2))" |
"validate_case _ = True"

(*To be checked: validating only receive inside single expression*)
fun validate_receive :: "expression ⇒ bool" where
"validate_receive (SingleExp (ReceiveExpr clauses _ _) _) = (∀c ∈ set clauses. length (get_patterns_list c) = 1)" |
"validate_receive _ = True"


fun get_function_names :: "function_definition list ⇒ annotated_function_name list" where
"get_function_names [] = []" |
"get_function_names ((FunctionDefinition fname _) # defs) =  fname # get_function_names defs"

fun validate_letrec :: "expression ⇒ bool" where
"validate_letrec (SingleExp(LetRecExpr defs _) None) = distinct (get_function_names defs)" |
"validate_letrec _ = True"

(*Clause and Patterns*)
fun extract_vars_from_annotated_pattern :: "annotated_pattern ⇒ variable_name list" where
"extract_vars_from_annotated_pattern (AnnotatedVarPattern var) = [extract_var_name var]"|
"extract_vars_from_annotated_pattern (AnnotatedPatern (AtomicLitPat _)) = []"|
"extract_vars_from_annotated_pattern (AnnotatedPatern (TuplePat patts)) = concat( map extract_vars_from_annotated_pattern patts)"|    
"extract_vars_from_annotated_pattern (AnnotatedPatern (ListPat patts)) = concat( map extract_vars_from_annotated_pattern patts)"|  
"extract_vars_from_annotated_pattern (AnnotatedPatern (BitstringPat patts)) = concat( map extract_vars_from_annotated_pattern patts)"|
"extract_vars_from_annotated_pattern (AnnotatedPatern (ListPatWithTail patts patt)) = concat( map extract_vars_from_annotated_pattern (patts@[patt]))"|
"extract_vars_from_annotated_pattern (AnnotatedPaternWithConst   (AtomicLitPat _) _) = []"|
"extract_vars_from_annotated_pattern (AnnotatedPaternWithConst   (TuplePat patts) _) =  concat( map extract_vars_from_annotated_pattern patts)"|
"extract_vars_from_annotated_pattern (AnnotatedPaternWithConst   (ListPat patts) _) =  concat( map extract_vars_from_annotated_pattern patts)"|
"extract_vars_from_annotated_pattern (AnnotatedPaternWithConst   (BitstringPat patts) _) =  concat( map extract_vars_from_annotated_pattern patts)"|
"extract_vars_from_annotated_pattern (AnnotatedPaternWithConst  (ListPatWithTail patts patt) _) =  concat( map extract_vars_from_annotated_pattern (patts@[patt]))"

(*
fun extract_vars_from_pattern :: "pattern ⇒ variable_name list" where
"extract_vars_from_pattern (AtomicLitPat _) = []" |
"extract_vars_from_pattern (TuplePat patts) = map extract_vars_from_annotated_pattern patts" |
"extract_vars_from_pattern (ListPat patts) = map extract_vars_from_annotated_pattern patts " |
"extract_vars_from_pattern (BitstringPat patts) = map extract_vars_from_annotated_pattern patts" |
"extract_vars_from_pattern (ListPatWithTail patts patt) =extract_vars_from_pattern patt @ (map extract_vars_from_annotated_pattern patts)"
*)

fun is_valid_clause_pattern :: "annotated_clause ⇒ bool " where
"is_valid_clause_pattern (Clause ( Pattern patt) _ _ _) = distinct (extract_vars_from_annotated_pattern patt) "|
"is_valid_clause_pattern (Clause ( PatternsList patts) _ _ _) = distinct (map extract_vars_from_annotated_pattern patts) "

fun is_valid_annotated_pattern :: "annotated_pattern ⇒ bool" where
"is_valid_annotated_pattern  (AnnotatedVarPattern var_name) = True" |
"is_valid_annotated_pattern  (AnnotatedPatern (AtomicLitPat atom)) = True" |
"is_valid_annotated_pattern _ = False"

fun is_valid_bitstring_pattern_expression :: "expression ⇒ bool" where
"is_valid_bitstring_pattern_expression (SingleExp (AtomicLitExpr _) None) = True" |
"is_valid_bitstring_pattern_expression  (SingleExp (VarNameExpr _)None) = True" |
"is_valid_bitstring_pattern_expression _ = False"


fun is_valid_bitstring_pattern :: "bitstring_pattern ⇒ bool" where
"is_valid_bitstring_pattern (BitstringPattern patt exps) = 
  (is_valid_annotated_pattern patt ∧ (∀exp ∈ set(map is_valid_bitstring_pattern_expression exps). exp) ∧ (length exps = BIT_SIZE))"


fun is_valid_guard :: "expression ⇒ bool" where
"is_valid_guard (SingleExp (ReceiveExpr _ _ _) _) = False" |
"is_valid_guard (SingleExp (AppExpr _ _) _) = False" |
"is_valid_guard (SingleExp (TryExpr e1 vars e2 catch_vars e3) None) = 
    (e3 = (SingleExp (AtomicLitExpr (AtomLiteral (Atom ([InputChar CHR ''f'']))))) None)" |
"is_valid_guard (SingleExp (TryExpr e1 (VariablesList vars) (ValueListExp (ValueList e2 _) _) catch_vars e3) (Some(Annotation annotation))) = 
    ((e3 = (SingleExp (AtomicLitExpr (AtomLiteral false)))
 ( Some(Annotation annotation)) )  ∧ (length vars = length e2))" |
"is_valid_guard (SingleExp (TryExpr _ _ _ _ _) _) = False"|
"is_valid_guard _ = True"

fun validate_clause :: "annotated_clause ⇒ bool" where
"validate_clause (Clause ps (When guard) body annotation) = 
  ((is_valid_clause_pattern((Clause ps (When guard) body annotation )) ∧ is_valid_guard guard ∧ is_valid_bitstring_pattern_expression body))"

section ‹Dynamic Semantics›
(* To be checked: vars are not considered values? lists and tuples could be included *)

(*Update: add another constructor of type exception Value could be exception*)

datatype exception = Error prim_op_call | Exit prim_op_call | Throw prim_op_call

datatype erlang_value =  AtomicValue atomic_literal |ExceptionValue exception 
 (* | ListValue "erlang_value list" |TupleValue  "erlang_value list" | BitStringValue  "erlang_value list" 
*)


(*Update: remove construct Exception *)
datatype result = Result  "erlang_value list"  | UndefinedBehaviour 

(*double check the representation *)
type_synonym env = "variable_name ⇒ erlang_value option"

(*Helper functions for lists & value_lists*)

fun is_value_result :: "result ⇒ bool" where
"is_value_result (Result [AtomicValue _]) = True" |
"is_value_result _ = False"


fun get_value_from_result :: "result ⇒ erlang_value" where
"get_value_from_result (Result [val]) = val" |
"get_value_from_result _ = undefined"

(*
fun is_exception :: "result  ⇒ bool" where
"is_exception (Result ((ExceptionValue _)#vals) =  " |
"is_exception _ = False"
*)

fun is_exception_value :: "erlang_value ⇒ bool" where
  "is_exception_value (ExceptionValue _) = True" |
 (* "is_exception_value (ListValue vals) = (∃v ∈ set vals. is_exception_value v)" |
  "is_exception_value (TupleValue vals) = (∃v ∈ set vals. is_exception_value v)" |*)
  "is_exception_value _ = False"

fun is_exception :: "result ⇒ bool" where
  "is_exception (Result vals) = (∃v ∈ set vals. is_exception_value v)" |
  "is_exception UndefinedBehaviour = False"


fun get_exception :: "result list ⇒ result" where
"get_exception (ex#results) = (if is_exception ex then ex else get_exception results)" |
"get_exception [] = UndefinedBehaviour"
(*
fun is_undefined :: "result ⇒ bool" where
"is_undefined (UndefinedBehaviour) = True" |
"is_undefined _ = False"*)

(*return undefined behaviour if it occurs at any point*)
fun handle_exceptions_or_undefined :: "result list ⇒ result" where
"handle_exceptions_or_undefined results =(if (UndefinedBehaviour \<in> set results) then UndefinedBehaviour
                                            else get_exception results )"

fun result_to_value_list :: "result ⇒ erlang_value list" where
"result_to_value_list (Result vs) = vs" |
"result_to_value_list _ = []"

fun sequence_results :: "result list ⇒ result" where
"sequence_results results = (if (list_all is_value_result results) then
                              Result (concat (map result_to_value_list results))
                            else handle_exceptions_or_undefined results)"

(*Helper function for let*)
(*could be improved by having a list of pairs *)
fun extend_env :: "env ⇒ variable_name list ⇒ result ⇒ env" where  
"extend_env env [] (Result []) = env" |
"extend_env env (var#vars) (Result ((AtomicValue atom) # vals)) =
  (λx. if x = var then Some (AtomicValue atom) else extend_env env vars (Result vals) x)" |
"extend_env env [var] (Result [ExceptionValue ex]) =
  (λx. if x = var then Some (ExceptionValue ex) else env x)" |
"extend_env _ _ _ = undefined"


(*pattern matching helpers *)
fun match_atomic :: "atomic_literal ⇒ erlang_value ⇒ bool" where
"match_atomic (IntegerLiteral intgr) (AtomicValue (IntegerLiteral iv )) = (intgr = iv)" |
"match_atomic (FloatLiteral float) (AtomicValue (FloatLiteral fv)) = (float = fv)" |
"match_atomic (AtomLiteral atom)(AtomicValue (AtomLiteral av)) = (atom = av)" |
"match_atomic (CharLiteral ch) (AtomicValue(CharLiteral cv)) = (ch = cv)" |
"match_atomic (NilLiteral (ErlangNil)) (AtomicValue (NilLiteral (ErlangNil))) = True" |
"match_atomic _ _ = False"




(*ToDo: implement match_bit_string*)
fun match_pattern :: "annotated_pattern list ⇒ erlang_value list ⇒ env ⇒ env option" where

"match_pattern [] [] env = Some env" |

"match_pattern ([AnnotatedVarPattern (AnnotatedVarName var)]) [val] env = Some(env(var ↦ val))" |

"match_pattern ([AnnotatedPatern (AtomicLitPat lit)])  [val] env =
   (if match_atomic lit val then Some env else None)" |

"match_pattern ([AnnotatedPatern (TuplePat (pat#pats))]) (val#vals) env =
   (case match_pattern [pat] [val] env of
      Some env' ⇒ match_pattern pats vals env'
    | None ⇒ None)" |
"match_pattern ([AnnotatedPatern(ListPat( pat#pats))]) ( val#vals) env =
   (case match_pattern [pat] [val] env of
      Some env' ⇒ match_pattern pats vals env'
    | None ⇒ None)" |
"match_pattern ([AnnotatedPatern(BitstringPat (pat#pats))]) (bval # vals) env =
   (case match_pattern [pat] [bval] env of
      Some env' ⇒ match_pattern pats vals env'
    | None ⇒ None)" |
"match_pattern ([AnnotatedPatern (ListPatWithTail (pat#pats) pat2)]) (val # vals) env =
   (case match_pattern [pat] [val] env of
      Some env' ⇒ match_pattern (pats@[pat2]) vals env'
    | None ⇒ None)" |
"match_pattern _ _ _ = None"

datatype select_case_result = 
    ClauseMatched "env * guard * expression" 
  | NoMatch


fun select_case :: "erlang_value list ⇒ annotated_clause  ⇒ env ⇒ select_case_result" where

"select_case case_values (Clause (Pattern patt)  guard body _)  env =
  (case match_pattern [patt] case_values env of
     Some env' ⇒ ClauseMatched (env', guard, body)
   | None ⇒NoMatch)"|

"select_case case_values (Clause (PatternsList patts)  guard body _)  env =
  (case match_pattern patts case_values env of
     Some env' ⇒ ClauseMatched (env', guard, body)
   | None ⇒NoMatch)"


fun get_annotated_variables ::" variables  ⇒ annotated_variable_name list" where
"get_annotated_variables (Variable var)  = [var]" |
"get_annotated_variables (VariablesList vars)  = vars"


(*Closure*)

datatype closure = Closure "variable_name list" expression env

fun create_closure :: "variable_name list ⇒ expression ⇒ env ⇒ closure" where
"create_closure params body env = Closure params body env"

fun extend_env_with_closure :: "env ⇒ function_name ⇒ closure ⇒ env" where
"extend_env_with_closure env fname closure = (λx. if x = fname then Some (AtomicValue (ClosureValue closure)) else env x)"



function erlang_eval :: "expression ⇒ env ⇒ result" where
  "erlang_eval (SingleExp (AtomicLitExpr lit) _) _ = Result [AtomicValue lit]" |

  "erlang_eval (SingleExp (VarNameExpr var) _) env =
     (case env var of
        Some val ⇒ Result [val]
      | None ⇒ UndefinedBehaviour)" |

  "erlang_eval (ValueListExp (ValueList exps _) _) env =
     (let vals = map (λe. erlang_eval (SingleExp e None) env) exps in
      if list_all is_value_result vals then
        Result (map get_value_from_result vals)
      else
        handle_exceptions_or_undefined vals)" |

  "erlang_eval (SingleExp (TupleExpr (Tuple exps)) _) env =
     (let vals = map (λe. erlang_eval e env) exps in
      if list_all is_value_result vals then
        Result (map get_value_from_result vals)
      else
        handle_exceptions_or_undefined vals)" |

  "erlang_eval (SingleExp (ListExpr (List (Nonemptylist exp exps))) _) env =
     (let vals = map (λe. erlang_eval e env) (exp # exps) in
      if list_all is_value_result vals then
        Result (map get_value_from_result vals)
      else
        handle_exceptions_or_undefined vals)" |

  "erlang_eval (SingleExp (ListExpr (ListWithTail (Nonemptylist exp1 exps) exp2)) _) env =
     (let vals = map (λe. erlang_eval e env) (exp1 # exps @ [exp2]) in
      if list_all is_value_result vals then
        Result (map get_value_from_result vals)
      else
        handle_exceptions_or_undefined vals)" |

  "erlang_eval (SingleExp (BinaryExp bitstr) _) env = undefined" |

  "erlang_eval (SingleExp (LetExpr (ErlangLet (VariablesList vars) e1 e2)) _) env =
     (case erlang_eval e1 env of
        Result [AtomicValue atom] ⇒
          if length vars = 1 then
            erlang_eval e2 (extend_env env (extract_var_name_list (VariablesList vars)) (Result [AtomicValue atom]))
          else
            UndefinedBehaviour
      | Result ((AtomicValue atom) # vals) ⇒
          if length ((AtomicValue atom) # vals) = length vars then
            erlang_eval e2 (extend_env env (extract_var_name_list (VariablesList vars)) (Result ((AtomicValue atom) # vals)))
          else
            UndefinedBehaviour
      | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (LetExpr (ErlangLet (Variable var) e1 e2)) _) env =
     (case erlang_eval e1 env of
        Result [AtomicValue atom] ⇒
          erlang_eval e2 (extend_env env (extract_var_name_list (VariablesList [var])) (Result [AtomicValue atom]))
      | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr [])) _) env = UndefinedBehaviour" |

  "erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr (cl # clauses))) _) env =
     (case erlang_eval switch_expr env of
        Result [AtomicValue atom] ⇒
          (case select_case [AtomicValue atom] cl env of
             ClauseMatched (env', When guard, body) ⇒
               (case erlang_eval guard env' of
                  Result [AtomicValue (AtomLiteral true)] ⇒ erlang_eval body env'
                | Result [AtomicValue (AtomLiteral false)] ⇒ erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env
                | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
                | UndefinedBehaviour ⇒ UndefinedBehaviour)
           | NoMatch ⇒ erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env)
      | Result ((AtomicValue atom) # vals) ⇒
          (case select_case ((AtomicValue atom) # vals) cl env of
             ClauseMatched (env', When guard, body) ⇒
               (case erlang_eval guard env' of
                  Result [AtomicValue (AtomLiteral true)] ⇒ erlang_eval body env'
                | Result [AtomicValue (AtomLiteral false)] ⇒ erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env
                | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
                | UndefinedBehaviour ⇒ UndefinedBehaviour)
           | NoMatch ⇒ erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env)
      | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (TryExpr expr vars try_expr catch_vars catch_expr) _) env =
     (case erlang_eval expr env of
        Result [AtomicValue atom] ⇒
          (case erlang_eval try_expr (extend_env env (map extract_var_name (get_annotated_variables vars)) (Result [AtomicValue atom])) of
             Result [AtomicValue atom] ⇒ Result [AtomicValue atom]
           | Result ((AtomicValue atom) # vals) ⇒ Result ((AtomicValue atom) # vals)
           | Result [ExceptionValue ex] ⇒
               erlang_eval catch_expr (extend_env env (map extract_var_name (get_annotated_variables catch_vars)) (Result [ExceptionValue ex]))
           | UndefinedBehaviour ⇒ UndefinedBehaviour)
      | Result ((AtomicValue atom) # vals) ⇒
          (case erlang_eval try_expr (extend_env env (map extract_var_name (get_annotated_variables vars)) (Result ((AtomicValue atom) # vals))) of
             Result [AtomicValue atom] ⇒ Result [AtomicValue atom]
           | Result ((AtomicValue atom) # vals) ⇒ Result ((AtomicValue atom) # vals)
           | Result [ExceptionValue ex] ⇒
               erlang_eval catch_expr (extend_env env (map extract_var_name (get_annotated_variables catch_vars)) (Result [ExceptionValue ex]))
           | UndefinedBehaviour ⇒ UndefinedBehaviour)
      | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (FuncNameExpr _) _) env = undefined" |

  "erlang_eval (SingleExp (FunExpr _) _) env = undefined" |
  "erlang_eval (SingleExp (LetRecExpr _ _) _) env = undefined" |
  "erlang_eval (SingleExp (AppExpr _ _) _) env = undefined" |
  "erlang_eval (SingleExp (InterModuleCallExpr _ _ _) _) env = undefined" |
  "erlang_eval (SingleExp (PrimOpCallExpr _ _ _) _) env = undefined" |
  "erlang_eval (SingleExp (ReceiveExpr _ _ _) _) env = undefined" |
  "erlang_eval (SingleExp (SequencingExpr _ _ ) _) env = undefined" |
  "erlang_eval (SingleExp (CatchExpr _) _) env = undefined"
  sorry
termination erlang_eval
  sorry



(**)


end