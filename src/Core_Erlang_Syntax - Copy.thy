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
                      | PrimOpCallExpr  atom  "expression list"
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

fun nat_to_digit :: "nat ⇒ digit" where
  "nat_to_digit num = (if num = 0 then Zero else
                    if num = 1 then One else
                    if num = 2 then Two else
                    if num = 3 then Three else
                    if num = 4 then Four else
                    if num = 5 then Five else
                    if num = 6 then Six else
                    if num = 7 then Seven else
                    if num = 8 then Eight else
                    if num = 9 then Nine else undefined)"

fun nat_to_nonemptylist :: "nat ⇒ digit nonemptylist" where
  "nat_to_nonemptylist num =
    (if num < 10 then Nonemptylist (nat_to_digit num) []
     else let q = num div 10;
              r = num mod 10
          in case nat_to_nonemptylist q of
               Nonemptylist head tail ⇒ Nonemptylist head (tail @ [nat_to_digit r]))"


fun nat_to_integer :: "nat ⇒ integer" where
  "nat_to_integer num = Integer None (nat_to_nonemptylist num)"



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



datatype exception = Error prim_op_call | Exit prim_op_call | Throw prim_op_call

datatype name = VarName variable_name | FuncName function_name

datatype erlang_value =  AtomicValue atomic_literal |ExceptionValue exception | ClosureValue closure
| ListValue "erlang_value list" | TupleValue  "erlang_value list" 
and env_entry = EnvValue erlang_value | EnvClosure closure
and env = Env "name ⇒ env_entry option"
and  closure = Closure "variable_name list" expression env
                      
datatype prim_op = AddOp | MulOp | SubOp| DivOp| EqualOp

datatype result = Result  "erlang_value list"  | UndefinedBehaviour 



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
(*use *list_ex*)
fun is_exception :: "result ⇒ bool" where
  "is_exception (Result vals) = (∃v ∈ set vals. is_exception_value v)" |
  "is_exception UndefinedBehaviour = False"


fun get_exception :: "result list ⇒ result" where
"get_exception (ex#results) = (if is_exception ex then ex else get_exception results)" |
"get_exception [] = UndefinedBehaviour"

fun is_undefined :: "result ⇒ bool" where
"is_undefined (UndefinedBehaviour) = True" |
"is_undefined _ = False"

(*use the is_undefined function above with list_all*)
(*return undefined behaviour if it occurs at any point*)
fun handle_exceptions_or_undefined :: "result list ⇒ result" where
" handle_exceptions_or_undefined results =(if list_ex is_undefined results then UndefinedBehaviour
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
(*type_synonym env = "name ⇒ erlang_value option"*)


(* Lookup an entry in the environment *)
fun lookup_env :: "env ⇒ name ⇒ env_entry option" where
  "lookup_env (Env env) name = env name"

(* Extend the environment with new variable-value bindings *)
fun extend_env :: "env ⇒ name list ⇒ erlang_value list ⇒ env" where
  "extend_env (Env env) [] [] = Env env" |
  "extend_env (Env env) (name#ns) (val#vals) =
    (let updated_env = (λx. if x = name then Some (EnvValue val) else env x) in
     extend_env (Env updated_env) ns vals)" |
  "extend_env _ _ _ = undefined"


fun extend_env_with_closure :: "env ⇒ name ⇒ closure ⇒ env" where
  "extend_env_with_closure (Env env) name closure =
     (Env (λx. if x = name then Some (EnvClosure closure) else env x))"




(*
fun extend_env :: "env ⇒ name list ⇒ erlang_value list ⇒ env" where
  "extend_env env [] [] = env" |
  "extend_env env (name#ns) (AtomicValue atom # vals) =
    (λx. if x = name then Some (AtomicValue atom) else extend_env env ns vals x)" |
  "extend_env env (name#ns) [ExceptionValue ex] =
    (λx. if x = name then Some (ExceptionValue ex) else env x)" |
  "extend_env _ _ _ = undefined"
*)

(*pattern matching helpers *)
fun match_atomic :: "atomic_literal ⇒ erlang_value ⇒ bool" where
"match_atomic (IntegerLiteral intgr) (AtomicValue (IntegerLiteral iv )) = (intgr = iv)" |
"match_atomic (FloatLiteral float) (AtomicValue (FloatLiteral fv)) = (float = fv)" |
"match_atomic (AtomLiteral atom)(AtomicValue (AtomLiteral av)) = (atom = av)" |
"match_atomic (CharLiteral ch) (AtomicValue(CharLiteral cv)) = (ch = cv)" |
"match_atomic (NilLiteral (ErlangNil)) (AtomicValue (NilLiteral (ErlangNil))) = True" |
"match_atomic _ _ = False"




(*ToDo: check matching lists and tuples*)

fun match_pattern :: "annotated_pattern list ⇒ erlang_value list ⇒ env ⇒ env option" where
  "match_pattern [] [] env = Some env" |

  "match_pattern ([AnnotatedVarPattern (AnnotatedVarName var)]) [val] env =
    Some (extend_env env [VarName var] [val])" |

  "match_pattern ([AnnotatedPatern (AtomicLitPat lit)]) [val] env =
    (if match_atomic lit val then Some env else None)" |

  "match_pattern ([AnnotatedPatern (TuplePat (pat#pats))]) (val#vals) env =
    (case match_pattern [pat] [val] env of
      Some env' ⇒ match_pattern pats vals env'
    | None ⇒ None)" |

  "match_pattern ([AnnotatedPatern (ListPat (pat#pats))]) (val#vals) env =
    (case match_pattern [pat] [val] env of
      Some env' ⇒ match_pattern pats vals env'
    | None ⇒ None)" |

  "match_pattern ([AnnotatedPatern (BitstringPat (pat#pats))]) (bval # vals) env =
    (case match_pattern [pat] [bval] env of
      Some env' ⇒ match_pattern pats vals env'
    | None ⇒ None)" |

  "match_pattern ([AnnotatedPatern (ListPatWithTail (pat#pats) pat2)]) (val # vals) env =
    (case match_pattern [pat] [val] env of
      Some env' ⇒ match_pattern (pats @ [pat2]) vals env'
    | None ⇒ None)" |

  "match_pattern _ _ _ = None"



datatype select_case_result = 
    ClauseMatched "env * guard * expression" 
  | NoMatch


fun select_case :: "erlang_value list ⇒ annotated_clause ⇒ env ⇒ select_case_result" where
  "select_case case_values (Clause (Pattern patt) guard body _) env =
    (case match_pattern [patt] case_values env of
      Some env' ⇒ ClauseMatched (env', guard, body)
    | None ⇒ NoMatch)" |

  "select_case case_values (Clause (PatternsList patts) guard body _) env =
    (case match_pattern patts case_values env of
      Some env' ⇒ ClauseMatched (env', guard, body)
    | None ⇒ NoMatch)"


fun get_annotated_variables ::" variables  ⇒ annotated_variable_name list" where
"get_annotated_variables (Variable var)  = [var]" |
"get_annotated_variables (VariablesList vars)  = vars"


(*Closure*)



fun create_closure :: "variable_name list ⇒ expression ⇒ env ⇒ closure" where
  "create_closure params body env = Closure params body env"

(* PrimeOpCall add, mult, and div *)
abbreviation add_atom :: atom where
  "add_atom ≡ Atom [InputChar (CHR ''a''), InputChar (CHR ''d''), InputChar (CHR ''d'')]"

abbreviation sub_atom :: atom where
  "sub_atom ≡ Atom [InputChar (CHR ''s''), InputChar (CHR ''u''), InputChar (CHR ''b'')]"

abbreviation div_atom :: atom where
  "div_atom ≡ Atom [InputChar (CHR ''d''), InputChar (CHR ''i''), InputChar (CHR ''v'')]"

abbreviation mul_atom :: atom where
  "mul_atom ≡ Atom [InputChar (CHR ''m''), InputChar (CHR ''u''), InputChar (CHR ''l'')]"

abbreviation equal_atom :: atom where
  "equal_atom ≡ Atom [InputChar (CHR ''e''), InputChar (CHR ''q''), InputChar (CHR ''u''), InputChar (CHR ''a''), InputChar (CHR ''l'')]"


(* Add two integers *)
fun add_integers :: "erlang_value list ⇒ erlang_value option" where
  "add_integers [AtomicValue (IntegerLiteral (Integer sign1 (Nonemptylist d1 ds1))), 
                 AtomicValue (IntegerLiteral (Integer sign2 (Nonemptylist d2 ds2)))] = 
    (let n1 = (case sign1 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d1 ds1)));
         n2 = (case sign2 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d2 ds2)));
         sum = n1 + n2;
         sign = (if sum < 0 then Some Minus else if sum = 0 then None else Some Plus);
         abs_sum = nat (abs sum)
     in Some (AtomicValue (IntegerLiteral (Integer sign (nat_to_nonemptylist abs_sum)))))" |
  "add_integers _ = None"

(* Multiply two integers *)
fun mul_integers :: "erlang_value list ⇒ erlang_value option" where
  "mul_integers [AtomicValue (IntegerLiteral (Integer sign1 (Nonemptylist d1 ds1))), 
                 AtomicValue (IntegerLiteral (Integer sign2 (Nonemptylist d2 ds2)))] = 
    (let n1 = (case sign1 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d1 ds1)));
         n2 = (case sign2 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d2 ds2)));
         prod = n1 * n2;
         sign = (if prod < 0 then Some Minus else if prod = 0 then None else Some Plus);
         abs_prod = nat (abs prod)
     in Some (AtomicValue (IntegerLiteral (Integer sign (nat_to_nonemptylist abs_prod)))))" |
  "mul_integers _ = None"

(* Divide two integers *)
fun div_integers :: "erlang_value list ⇒ erlang_value option" where
  "div_integers [AtomicValue (IntegerLiteral (Integer sign1 (Nonemptylist d1 ds1))), 
                 AtomicValue (IntegerLiteral (Integer sign2 (Nonemptylist d2 ds2)))] = 
    (let n1 = (case sign1 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d1 ds1)));
         n2 = (case sign2 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d2 ds2)));
         quotient = (if n2 ≠ 0 then n1 div n2 else 0);
         sign = (if quotient < 0 then Some Minus else if quotient = 0 then None else Some Plus);
         abs_quotient = nat (abs quotient)
     in (if n2 ≠ 0 then Some (AtomicValue (IntegerLiteral (Integer sign (nat_to_nonemptylist abs_quotient)))) else None))" |
  "div_integers _ = None"

(* Subtract two integers *)
fun sub_integers :: "erlang_value list ⇒ erlang_value option" where
  "sub_integers [AtomicValue (IntegerLiteral (Integer sign1 (Nonemptylist d1 ds1))), 
                 AtomicValue (IntegerLiteral (Integer sign2 (Nonemptylist d2 ds2)))] = 
    (let n1 = (case sign1 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d1 ds1)));
         n2 = (case sign2 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d2 ds2)));
         diff = n1 - n2;
         sign = (if diff < 0 then Some Minus else if diff = 0 then None else Some Plus);
         abs_diff = nat (abs diff)
     in Some (AtomicValue (IntegerLiteral (Integer sign (nat_to_nonemptylist abs_diff)))))" |
  "sub_integers _ = None"

(* Check if two integers are equal *)
fun equal_integers :: "erlang_value list ⇒ erlang_value option" where
  "equal_integers [AtomicValue (IntegerLiteral (Integer sign1 (Nonemptylist d1 ds1))), 
                   AtomicValue (IntegerLiteral (Integer sign2 (Nonemptylist d2 ds2)))] = 
    (let n1 = (case sign1 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d1 ds1)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d1 ds1)));
         n2 = (case sign2 of None ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Plus ⇒ int (nonemptylist_to_nat (Nonemptylist d2 ds2)) 
                            | Some Minus ⇒ - int (nonemptylist_to_nat (Nonemptylist d2 ds2)));
         is_equal = (n1 = n2)
     in if is_equal then Some (AtomicValue (AtomLiteral true)) 
                    else Some (AtomicValue (AtomLiteral  false))
    )" |
  "equal_integers _ = None"

(* Evaluate primitive operations *)

fun eval_prim_op :: "prim_op ⇒ erlang_value list ⇒ erlang_value option" where
  "eval_prim_op AddOp args = add_integers args" |
  "eval_prim_op SubOp args = sub_integers args" |
  "eval_prim_op MulOp args = mul_integers args" |
  "eval_prim_op DivOp args = div_integers args" |
  "eval_prim_op EqualOp args = equal_integers args" 



function erlang_eval :: "expression ⇒ env ⇒ result" where
  "erlang_eval (SingleExp (AtomicLitExpr lit)_) env = Result [AtomicValue lit]" |

  "erlang_eval (SingleExp (VarNameExpr var)_) env = 
     (case lookup_env env (VarName var) of
        Some (EnvValue val) ⇒ Result [val]
      | _ ⇒ UndefinedBehaviour)" |

  "erlang_eval (ValueListExp (ValueList exps _)  _) env = 
     (let vals = map (λe. erlang_eval (SingleExp e None) env) exps in
      if (list_all is_value_result vals) then Result (map get_value_from_result vals)
      else handle_exceptions_or_undefined vals)" |

  "erlang_eval (SingleExp(TupleExpr (Tuple exps))_) env = 
     (let vals = map (λe. erlang_eval e env) exps in
      if (list_all is_value_result vals) then Result (map get_value_from_result vals)
      else handle_exceptions_or_undefined vals)" |

  "erlang_eval  (SingleExp (ListExpr (List(Nonemptylist exp exps)))_) env = 
     (let vals = map (λe. erlang_eval e env) (exp#exps) in
      if (list_all is_value_result vals) then Result (map get_value_from_result vals)
      else handle_exceptions_or_undefined vals)" |

  "erlang_eval  (SingleExp (ListExpr (ListWithTail(Nonemptylist exp1 exps) exp2 ))_) env = 
     (let vals = map (λe. erlang_eval e env) (exp1#exps @ [exp2]) in
      if (list_all is_value_result vals) then Result (map get_value_from_result vals)
      else handle_exceptions_or_undefined vals)"  |

  "erlang_eval  (SingleExp (BinaryExp bitstr) _) env = undefined" |

  "erlang_eval (SingleExp (LetExpr (ErlangLet (VariablesList vars) e1 e2)) _) env =
     (case erlang_eval e1 env of
        Result [AtomicValue atom] ⇒ 
          if length vars = 1 then
            erlang_eval e2 (extend_env env (map VarName (map extract_var_name (get_annotated_variables (VariablesList vars)))) [AtomicValue atom])
          else UndefinedBehaviour
      | Result ((AtomicValue atom) # vals) ⇒ 
          if length ((AtomicValue atom) # vals) = length vars then
            erlang_eval e2 (extend_env env (map VarName (map extract_var_name (get_annotated_variables (VariablesList vars)))) ((AtomicValue atom) # vals))
          else UndefinedBehaviour
      | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (LetExpr (ErlangLet (Variable var) e1 e2)) _) env =
     (case erlang_eval e1 env of
        Result [AtomicValue atom] ⇒
          erlang_eval e2 (extend_env env [VarName (extract_var_name var)] [AtomicValue atom])
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
                | Result [AtomicValue (AtomLiteral false)] ⇒ 
                    erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env
                | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
                | UndefinedBehaviour ⇒ UndefinedBehaviour)
           | NoMatch ⇒ erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env)
      | Result ((AtomicValue atom) # vals) ⇒ 
          (case select_case ((AtomicValue atom) # vals) cl env of
             ClauseMatched (env', When guard, body) ⇒
               (case erlang_eval guard env' of
                  Result [AtomicValue (AtomLiteral true)] ⇒ erlang_eval body env'
                | Result [AtomicValue (AtomLiteral false)] ⇒ 
                    erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env
                | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
                | UndefinedBehaviour ⇒ UndefinedBehaviour)
           | NoMatch ⇒ erlang_eval (SingleExp (CaseExpr (ErlangCase switch_expr clauses)) None) env)
      | Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (TryExpr expr vars try_expr catch_vars catch_expr) _) env =
     (case erlang_eval expr env of
        Result [AtomicValue atom] ⇒ 
          (case erlang_eval try_expr (extend_env env (map VarName (map extract_var_name (get_annotated_variables vars))) [AtomicValue atom]) of
             Result [AtomicValue atom] ⇒ Result [AtomicValue atom]
           | Result ((AtomicValue atom) # vals) ⇒ Result ((AtomicValue atom) # vals)
           | Result [ExceptionValue ex] ⇒ 
               erlang_eval catch_expr (extend_env env (map VarName (map extract_var_name (get_annotated_variables catch_vars))) [ExceptionValue ex])
           | UndefinedBehaviour ⇒ UndefinedBehaviour)
      | Result ((AtomicValue atom) # vals) ⇒ 
          (case erlang_eval try_expr (extend_env env (map VarName (map extract_var_name (get_annotated_variables vars))) ((AtomicValue atom) # vals)) of
             Result [AtomicValue atom] ⇒ Result [AtomicValue atom]
           | Result ((AtomicValue atom) # vals) ⇒ Result ((AtomicValue atom) # vals)
           | Result [ExceptionValue ex] ⇒ 
               erlang_eval catch_expr (extend_env env (map VarName (map extract_var_name (get_annotated_variables catch_vars))) [ExceptionValue ex])
           | UndefinedBehaviour ⇒ UndefinedBehaviour)
      | Result [ExceptionValue ex] ⇒ 
          erlang_eval catch_expr (extend_env env (map VarName (map extract_var_name (get_annotated_variables catch_vars))) [ExceptionValue ex])
      | UndefinedBehaviour ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (FuncNameExpr func_name) _) env = 
     (case lookup_env env (FuncName func_name) of
        Some (EnvClosure closure) ⇒ Result [ClosureValue closure]
      | _ ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (FunExpr (Func params body)) _) env = 
     Result [ClosureValue (create_closure (map extract_var_name params) body env)]" |


  "erlang_eval (SingleExp (AppExpr func_expr arg_exprs) _) env = 
     (case erlang_eval func_expr env of
        Result [ClosureValue (Closure params body closure_env)] ⇒
          if length params = length arg_exprs then
            let arg_vals = map (λarg. case erlang_eval arg env of Result [val] ⇒ val | _ ⇒ undefined) arg_exprs in
            erlang_eval body (extend_env closure_env (map VarName params) arg_vals)
          else UndefinedBehaviour
      | _ ⇒ UndefinedBehaviour)" |

  "erlang_eval (SingleExp (CatchExpr expr) _) env = 
     (case erlang_eval expr env of
        Result [ExceptionValue ex] ⇒ Result [ExceptionValue ex]
      | result ⇒ result)" |

 "erlang_eval (SingleExp (LetRecExpr defs expr) _) env =
     (let
        func_names = map extract_function_name defs;
        func_closures = map (λdef. create_closure (map extract_var_name (get_fun_params def)) (extract_def_body def) env) defs;
        new_env = foldl (λacc (name, closure). extend_env_with_closure acc (FuncName name) closure)
                        env (zip func_names func_closures)
      in
        erlang_eval expr new_env)" |

"erlang_eval (SingleExp (PrimOpCallExpr prim_op  exprs) _) env =
     (let vals = map (λe. erlang_eval e env) exprs;
          pri_op = if prim_op = add_atom then AddOp else 
            if prim_op = sub_atom then SubOp else
             if prim_op = mul_atom then MulOp else
             if prim_op = div_atom then DivOp else
             if prim_op = equal_atom then EqualOp else undefined in
      if list_all is_value_result vals then
        case eval_prim_op pri_op (map get_value_from_result vals) of
           Some(AtomicValue atom)  ⇒  Result [AtomicValue atom]
        | Some(ExceptionValue ex) ⇒  Result [ExceptionValue ex]
        | None ⇒ UndefinedBehaviour
      else handle_exceptions_or_undefined vals)" |

  "erlang_eval (SingleExp (InterModuleCallExpr module_expr func_expr args) _) env = 
undefined
" |
  "erlang_eval (SingleExp (ReceiveExpr _ _ _) _) env = 
undefined
" |
  "erlang_eval (SingleExp (SequencingExpr _ _) _) env = 
undefined
"
  sorry
termination erlang_eval
  sorry



subsection  \<open>Simple Expressions\<close>

(* Example of atoms *)
definition atom_example_1 :: atom where
"atom_example_1 = Atom [InputChar CHR ''a'', InputChar CHR ''t'', InputChar CHR ''o'', InputChar CHR ''m'']"

definition atom_example_2 :: atom where
"atom_example_2 = Atom [InputChar CHR ''e'', InputChar CHR ''r'', InputChar CHR ''l'', InputChar CHR ''a'', InputChar CHR ''n'', InputChar CHR ''g'']"

definition atomic_exp_example_1 :: expression where
"atomic_exp_example_1 = SingleExp (AtomicLitExpr (AtomLiteral atom_example_1)) None"

definition atomic_exp_example_2 :: expression where
"atomic_exp_example_2 = SingleExp (AtomicLitExpr (AtomLiteral atom_example_2)) None"


(* Example of integers *)
definition int_example_1 :: integer where
"int_example_1 = Integer (Some Plus) (Nonemptylist One [Zero])"  (* 10 *)

definition int_example_2 :: integer where
"int_example_2 = Integer (Some Minus) (Nonemptylist Five [Three])"  (* -53 *)

definition int_example_3 :: integer where
"int_example_3 = Integer (Some Plus) (Nonemptylist Three [])"  (* 3 *)

definition int_example_4 :: integer where
"int_example_4 = Integer (Some Plus) (Nonemptylist Four [])"  (* 4 *)

definition int_exp_example_1 :: "expression" where
  "int_exp_example_1 = SingleExp (AtomicLitExpr (IntegerLiteral int_example_1)) None"

definition int_exp_example_2 :: "expression" where
  "int_exp_example_2 = SingleExp (AtomicLitExpr (IntegerLiteral int_example_2)) None"

definition int_exp_example_3 :: "expression" where
  "int_exp_example_3 = SingleExp (AtomicLitExpr (IntegerLiteral int_example_3)) None"

definition int_exp_example_4 :: "expression" where
  "int_exp_example_4 = SingleExp (AtomicLitExpr (IntegerLiteral int_example_4)) None"


(* Example of variables *)
definition var_example_1 :: variable_name where
"var_example_1 = UpperCharVar A [Lowercase v, Lowercase a, Lowercase r]"

definition var_example_2 :: variable_name where
"var_example_2 = UnderscoreVar (Nonemptylist Underscore [Digit Zero])"

definition var_exp_example_1 :: "expression" where
  "var_exp_example_1 = SingleExp (VarNameExpr var_example_1 ) None"

definition var_exp_example_2 :: "expression" where
  "var_exp_example_2 = SingleExp (VarNameExpr var_example_2 ) None"


(* Example environment *)
definition env_example :: env where
"env_example = Env (\<lambda>x. if x = VarName var_example_1 then
 Some (EnvValue (AtomicValue (IntegerLiteral int_example_1))) else if
 x = VarName var_example_2 then
 Some (EnvValue (AtomicValue (IntegerLiteral int_example_2)))else None)"


(* Add function: add(x, y) -> x + y *)
definition add_fun :: func where
"add_fun = Func [AnnotatedVarName var_example_1, AnnotatedVarName var_example_2]
                (SingleExp (PrimOpCallExpr add_atom [var_exp_example_1, var_exp_example_2]) None)"

abbreviation two :: integer where
  "two ≡ Integer None (Nonemptylist Two [])"

(* Define the function name for the add function *)
definition add_function_name :: function_name where
  "add_function_name ≡ FunctionName add_atom two"

(* Define the function definition for the add function *)
definition add_fun_def :: function_definition where
  "add_fun_def ≡ FunctionDefinition (AnnotatedFunctionName add_function_name None) 
                                     (AnnotatedFun add_fun None)"

(* Define the module that contains the add function *)
definition add_module :: module where
  "add_module ≡ Module add_atom 
                       (ModuleHeader [Export add_function_name] []) 
                       (ModuleBody [add_fun_def]) 
                       End"

(* Define the environment that includes the add function *)
definition add_env :: env where
  "add_env ≡ Env (λname. if name = FuncName add_function_name 
                        then Some (EnvClosure (Closure 
                                                [var_example_1, var_example_2] 
                                                (SingleExp (PrimOpCallExpr  add_atom [var_exp_example_1, var_exp_example_2]) None) 
                                                (Env (λ_. None))))
                        else None)"

(* Define the test expression to add 3 and 5 using the add function *)
definition test_add_expr :: expression where
  "test_add_expr ≡ SingleExp 
                    (AppExpr 
                      (SingleExp (FuncNameExpr add_function_name) None) 
                      [(SingleExp (AtomicLitExpr (IntegerLiteral (nat_to_integer 3))) None), 
                       (SingleExp (AtomicLitExpr (IntegerLiteral (nat_to_integer 5))) None)]) 
                    None"

(* Evaluate the test expression *)
definition add_result :: result where
  "add_result ≡ erlang_eval test_add_expr add_env"

value "add_result"


(* Define factorial function using Core Erlang syntax *)
abbreviation factorial_atom :: atom where
  "factorial_atom ≡ Atom [InputChar (CHR ''f''), InputChar (CHR ''a''), InputChar (CHR ''c''), InputChar (CHR ''t''), InputChar (CHR ''o''), InputChar (CHR ''r''), InputChar (CHR ''i''), InputChar (CHR ''a''), InputChar (CHR ''l'')]"

abbreviation main_atom :: atom where
  "main_atom ≡ Atom [InputChar (CHR ''m''), InputChar (CHR ''a''), InputChar (CHR ''i''), InputChar (CHR ''n'')]"

abbreviation zero_atom :: atom where
  "zero_atom ≡ Atom [InputChar (CHR ''z''), InputChar (CHR ''e''), InputChar (CHR ''r''), InputChar (CHR ''o'')]"

abbreviation one_atom :: atom where
  "one_atom ≡ Atom [InputChar (CHR ''o''), InputChar (CHR ''n''), InputChar (CHR ''e'')]"

abbreviation zero :: integer where
  "zero ≡ Integer None (Nonemptylist Zero [])"

abbreviation one :: integer where
  "one ≡ Integer None (Nonemptylist One [])"

abbreviation three :: integer where
  "three ≡ Integer None (Nonemptylist Three [])"

abbreviation x_var :: variable_name where
  "x_var ≡ UpperCharVar X []"

abbreviation fact_var :: variable_name where
  "fact_var ≡ UpperCharVar A []"

definition empty_env :: env where
  "empty_env ≡ Env (λx. None)"

definition env_fact :: env where
"env_fact = Env (\<lambda>x. if x = VarName x_var then
 Some (EnvValue (AtomicValue (IntegerLiteral int_example_1))) else  None)"


 (*gaurd for the second clause could be t*)

definition factorial_fun :: func where
  "factorial_fun ≡ Func 
     [AnnotatedVarName x_var] 
     (SingleExp 
       (CaseExpr 
         (ErlangCase 
           (SingleExp (VarNameExpr x_var) None) 
           [Clause 
             (Pattern (AnnotatedPatern (AtomicLitPat (IntegerLiteral (Integer None (Nonemptylist Zero [])))))) 
             (When (SingleExp (AtomicLitExpr (AtomLiteral true)) None)) 
             (SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist One [])))) None) 
             [], 
            Clause 
              (Pattern (AnnotatedVarPattern (AnnotatedVarName x_var))) 
                (When (SingleExp (AtomicLitExpr (AtomLiteral true)) None))
              ( SingleExp 
                (PrimOpCallExpr mul_atom 
                  [(SingleExp (VarNameExpr x_var) None),
                   (SingleExp 
                     (AppExpr 
                       (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None) 
                       [(SingleExp 
                          (PrimOpCallExpr  sub_atom 
                            [(SingleExp (VarNameExpr x_var) None), 
                             (SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist (nat_to_digit 1) [])))) None)]) None)]) None)]) 
               None)[] ])) None)"

definition factorial_fun_def :: function_definition where
  "factorial_fun_def ≡ FunctionDefinition 
    (AnnotatedFunctionName (FunctionName factorial_atom one) None)
    (AnnotatedFun factorial_fun None)"

(* Define the module containing the factorial function *)
definition factorial_module :: module where
  "factorial_module ≡ Module 
    factorial_atom 
    (ModuleHeader [Export (FunctionName factorial_atom one)] []) 
    (ModuleBody [factorial_fun_def]) 
    End"

(* Create the environment with the factorial function *)
definition factorial_env :: env where
  "factorial_env ≡ Env (λname. if name = FuncName (FunctionName factorial_atom one) 
   then Some (EnvClosure (Closure [x_var]
      (SingleExp  (CaseExpr 
         (ErlangCase 
           (SingleExp (VarNameExpr x_var) None) 
           [Clause 
             (Pattern (AnnotatedPatern (AtomicLitPat (IntegerLiteral (Integer None (Nonemptylist Zero [])))))) 
             (When (SingleExp (AtomicLitExpr (AtomLiteral true)) None)) 
             (SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist One [])))) None) 
             [], 
            Clause 
              (Pattern (AnnotatedVarPattern (AnnotatedVarName x_var))) 
              (When (SingleExp (AtomicLitExpr (AtomLiteral true)) None)) 
              ( SingleExp 
                (PrimOpCallExpr mul_atom 
                  [(SingleExp (VarNameExpr x_var) None),
                   (SingleExp 
                     (AppExpr 
                       (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None) 
                       [(SingleExp 
                          (PrimOpCallExpr  sub_atom 
                            [(SingleExp (VarNameExpr x_var) None), 
                             (SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist (nat_to_digit 1) [])))) None)]) None)]) None)]) 
               None)[] ])) None)  
     (Env (λ_. None)))) 
   else if name = VarName x_var then
 Some (EnvValue (AtomicValue (IntegerLiteral two))) else  None)"

(* Define the testexpression to calculate factorial of 5 *)
definition test_factorial_expr :: expression where
  "test_factorial_expr ≡ SingleExp 
    (AppExpr 
      (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None) 
      [(SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist One [])))) None)]) 
    None"

(* Evaluate the test expression *)
definition factorial_result :: result where
  "factorial_result ≡ erlang_eval test_factorial_expr factorial_env"

(* Check the result *)
value "factorial_result"

value"erlang_eval  (SingleExp (VarNameExpr x_var) None) factorial_env  "



value "select_case [AtomicValue (IntegerLiteral zero)] (Clause 
             (Pattern (AnnotatedPatern (AtomicLitPat (IntegerLiteral (Integer None (Nonemptylist Zero [])))))) 
             (When (SingleExp (AtomicLitExpr (AtomLiteral true)) None)) 
             (SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist One [])))) None) 
             []) factorial_env"

value "select_case [AtomicValue (IntegerLiteral one)] (Clause 
              (Pattern (AnnotatedVarPattern (AnnotatedVarName x_var))) 
              (When (SingleExp (AtomicLitExpr (AtomLiteral true)) None)) 
              ( SingleExp 
                (PrimOpCallExpr mul_atom 
                  [(SingleExp (VarNameExpr x_var) None),
                   (SingleExp 
                     (AppExpr 
                       (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None) 
                       [(SingleExp 
                          (PrimOpCallExpr  sub_atom 
                            [(SingleExp (VarNameExpr x_var) None), 
                             (SingleExp (AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist (nat_to_digit 1) [])))) None)]) None)]) None)]) 
               None)[]) factorial_env"

value "erlang_eval (SingleExp
    (PrimOpCallExpr mul_atom
      [SingleExp (VarNameExpr x_var) None,
       SingleExp
        (AppExpr (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None)
          [SingleExp
            (PrimOpCallExpr sub_atom
              [SingleExp (VarNameExpr x_var) None, SingleExp (AtomicLitExpr (IntegerLiteral one)) None])
            None])
        None])
    None) factorial_env "

value "erlang_eval (SingleExp
    (PrimOpCallExpr mul_atom
      [SingleExp (VarNameExpr x_var) None, (SingleExp (AtomicLitExpr (IntegerLiteral (nat_to_integer 3))) None) ])
    None) factorial_env "

value "erlang_eval (SingleExp
            (PrimOpCallExpr sub_atom
              [SingleExp (VarNameExpr x_var) None, SingleExp (AtomicLitExpr (IntegerLiteral one)) None])
            None) factorial_env"

value "erlang_eval ( SingleExp
        (AppExpr (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None)
          [SingleExp
            (PrimOpCallExpr sub_atom
              [SingleExp (VarNameExpr x_var) None, SingleExp (AtomicLitExpr (IntegerLiteral one)) None])
            None])
        None) factorial_env"

value "erlang_eval ( SingleExp
        (AppExpr (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None)
          [ SingleExp (AtomicLitExpr (IntegerLiteral zero)) None])
        None) factorial_env"

value"erlang_eval (SingleExp (AtomicLitExpr (AtomLiteral true)) None) (empty_env) "

value "erlang_eval ( SingleExp (AtomicLitExpr (IntegerLiteral one)) None) factorial_env"

value"erlang_eval (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None) factorial_env"

(*Let Expression*)
(* Let expression: let x = 10 in x + 10 *)
definition let_expr :: expression where
"let_expr = SingleExp (LetExpr (ErlangLet (Variable (AnnotatedVarName var_example_1)) int_exp_example_1
                            (SingleExp (PrimOpCallExpr add_atom
                                        [ var_exp_example_1, int_exp_example_1 ]) None))) None"

definition let_add_example :: expression where
  "let_add_example ≡ SingleExp 
     (LetExpr 
       (ErlangLet 
         (VariablesList [AnnotatedVarName x_var, AnnotatedVarName fact_var]) 
         (ValueListExp (ValueList 
           [AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist Three []))) , 
            AtomicLitExpr (IntegerLiteral (Integer None (Nonemptylist Four []))) ] 
           None) None) 
         (SingleExp 
           (AppExpr 
             (SingleExp (FuncNameExpr (FunctionName add_atom (Integer None (Nonemptylist Two [])))) None) 
             [SingleExp (VarNameExpr x_var) None, 
              SingleExp (VarNameExpr fact_var) None]) 
           None))) 
     None"


(*List Operations*)
definition append_fun :: func where
  "append_fun ≡ Func 
     [AnnotatedVarName x_var, AnnotatedVarName fact_var] 
     (SingleExp 
       (ListExpr 
         (ListWithTail 
           (Nonemptylist 
             (SingleExp (VarNameExpr x_var) None) 
             [SingleExp (VarNameExpr fact_var) None]) 
           (SingleExp (AtomicLitExpr (NilLiteral (ErlangNil))) None)) 
       ) None)"

definition reverse_fun :: func where
  "reverse_fun ≡ Func 
     [AnnotatedVarName x_var] 
     (SingleExp 
       (CaseExpr 
         (ErlangCase 
           (SingleExp (VarNameExpr x_var) None) 
           [Clause 
             (Pattern (AnnotatedPatern (ListPat []))) 
             (When (SingleExp (AtomicLitExpr (AtomLiteral zero_atom)) None)) 
             (SingleExp (AtomicLitExpr (NilLiteral (ErlangNil))) None) 
             [], 
            Clause 
              (Pattern (AnnotatedPatern (ListPat [AnnotatedVarPattern (AnnotatedVarName fact_var)]))) 
              (When (SingleExp (AtomicLitExpr (AtomLiteral zero_atom)) None)) 
              (SingleExp 
                (AppExpr 
                  (SingleExp (FuncNameExpr (FunctionName factorial_atom one)) None) 
                  [(SingleExp (VarNameExpr fact_var) None)]) 
                None) 
              []])) 
       None)"



value "add_fun"
value "integer_to_nat int_example_2 + integer_to_nat int_example_1"

(*11*)


end