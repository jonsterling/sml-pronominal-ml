structure PmlParamSort : 
sig
  datatype param_sort = SYM
  include ABT_SORT where type t = param_sort
end =
struct
  datatype param_sort = SYM
  type t = param_sort
  val eq : t * t -> bool = op=
  fun toString SYM = "sym"
end

structure PmlParam : ABT_PARAMETER = AbtEmptyParameter (PmlParamSort)

structure PmlSort :
sig
  datatype sort = CTYP | VTYP | EXP
  include ABT_SORT where type t = sort
end =
struct
  datatype sort = CTYP | VTYP | EXP
  type t = sort
  val eq : t * t -> bool = op=

  val toString = 
    fn CTYP => "ctyp"
     | VTYP => "vtyp"
     | EXP => "exp"
end

structure PmlArity = ListAbtArity (structure S = PmlSort and PS = PmlParamSort)
structure PmlParamTerm = AbtParameterTerm (PmlParam)

structure ArityNotation =
struct
  fun op* (a, b) = (a, b) (* symbols sorts, variable sorts *)
  fun op<> (a, b) = (a, b) (* valence *)
  fun op->> (a, b) = (a, b) (* arity *)
end

structure PmlOperator :
sig
  datatype pat = 
     PAT_PLUS
   | PAT_TENSOR
   | PAT_ABS
   | PAT_ONE
   | PAT_VAR

  datatype 'a operator = 
     PAIR | TT | INL | INR | SYMREF of 'a
   | ABS | SWAP of 'a * 'a
   | NU | LAM | AP
   | PM of pat
   | TENSOR | PLUS | FN | ONE | ATOM

  include ABT_OPERATOR where type 'a t = 'a operator
end =
struct
  structure P = PmlParamTerm and Ar = PmlArity

  datatype pat =
     PAT_PLUS
   | PAT_TENSOR
   | PAT_ABS
   | PAT_ONE
   | PAT_VAR

  datatype 'a operator = 
     PAIR | TT | INL | INR | SYMREF of 'a
   | ABS | SWAP of 'a * 'a
   | NU | LAM | AP
   | PM of pat
   | TENSOR | PLUS | FN | ONE | ATOM

  type 'a t = 'a operator

  local
    open ArityNotation PmlParamSort PmlSort
    infix <> ->>
  in
    fun arity th =
      case th of
         PAIR => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
       | TT => [] ->> EXP
       | INL => [[] * [] <> EXP] ->> EXP
       | INR => [[] * [] <> EXP] ->> EXP
       | SYMREF _ => [] ->> EXP
       | ABS => [[SYM] * [] <> EXP] ->> EXP
       | SWAP _ => [[] * [] <> EXP] ->> EXP
       | NU => [[SYM] * [] <> EXP] ->> EXP
       | LAM => [[] * [EXP] <> EXP] ->> EXP
       | AP => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
       | PM PAT_PLUS => [[] * [] <> EXP, [] * [EXP] <> EXP, [] * [EXP] <> EXP] ->> EXP
       | PM PAT_TENSOR => [[] * [] <> EXP, [] * [EXP,EXP] <> EXP] ->> EXP
       | PM PAT_ABS => [[] * [] <> EXP, [SYM] * [EXP] <> EXP] ->> EXP
       | PM PAT_ONE => [[] * [] <> EXP, [] * [] <> EXP] ->> EXP
       | PM PAT_VAR => [[] * [] <> EXP, [] * [EXP] <> EXP] ->> EXP
       | TENSOR => [[] * [] <> VTYP, [] * [] <> VTYP] ->> VTYP
       | PLUS => [[] * [] <> VTYP, [] * [] <> VTYP] ->> VTYP
       | FN => [[] * [] <> VTYP, [] * [] <> CTYP] ->> CTYP
       | ONE => [] ->> VTYP
       | ATOM => [] ->> VTYP
  end

  local
    open PmlParamSort
  in
    fun support th =
      case th of
         SYMREF a => [(a, SYM)]
       | SWAP (a, b) => [(a, SYM), (b, SYM)]
       | _ => []
  end

  fun eq f = 
    fn (PAIR, PAIR) => true
     | (TT, TT) => true
     | (INL, INL) => true
     | (INR, INR) => true
     | (SYMREF a, SYMREF b) => f (a, b)
     | (ABS, ABS) => true
     | (SWAP (a1, a2), SWAP (b1, b2)) => f (a1, b1) andalso f (a2, b2)
     | (NU, NU) => true
     | (LAM, LAM) => true
     | (AP, AP) => true
     | (PM pat1, PM pat2) => pat1 = pat2
     | (TENSOR, TENSOR) => true
     | (PLUS, PLUS) => true
     | (FN, FN) => true
     | (ONE, ONE) => true
     | (ATOM, ATOM) => true

  fun toString f = 
    fn PAIR => "pair"
     | TT => "tt"
     | INL => "inl"
     | INR => "inr"
     | SYMREF a => "&" ^ f a
     | ABS => "abs"
     | SWAP (a, b) => "{" ^ f a ^ " <-> " ^ f b ^ "}"
     | PM _ => "pm"
     | TENSOR => "tensor"
     | PLUS => "plus"
     | FN => "fn"
     | ONE => "one"
     | ATOM => "atom"

  local
    open PmlParamTerm
  in
    fun map f = 
      fn PAIR => PAIR
      | TT => TT
      | INL => INL
      | INR => INR
      | SYMREF a => let val VAR a' = f a in SYMREF a' end
      | ABS => ABS
      | SWAP (a, b) => let val (VAR a', VAR b') = (f a, f b) in SWAP (a', b') end
      | PM pat => PM pat
      | TENSOR => TENSOR
      | PLUS => PLUS
      | FN => FN
      | ONE => ONE
      | ATOM => ATOM
  end
end

local
  structure AbtKit =
  struct
    structure O = PmlOperator
      and Metavar = AbtSymbol ()
      and Var = AbtSymbol ()
      and Sym = AbtSymbol ()
    type annotation = Pos.t
  end

  structure AstKit =
  struct
    structure Operator = PmlOperator
    structure Metavar = StringAbtSymbol
    type annotation = Pos.t
  end
in
  structure PmlAbt = Abt (AbtKit)
  structure PmlAst = AstUtil (Ast (AstKit))
  structure PmlAstToAbt = AstToAbt (structure Abt = PmlAbt and Ast = PmlAst)
end

