signature PML_MACHINE =
sig
  type 'a appview

  type val_
  type cmp

  type 'a closure
  datatype 'a slot = HOLE | DONE of 'a | AWAIT of 'a closure
  type 'a frame = 'a slot appview
  type 'a stack = 'a frame list

  datatype cfg = 
     <| of cmp closure * cmp stack
   | |> of val_ closure * cmp stack

  val init : cmp -> cfg
  val step : cfg -> cfg option
end

structure PmlMachine : PML_MACHINE =
struct
  structure Cl = AbtClosureUtil (AbtClosure (PmlAbt))
  open Cl PmlAbt
  structure O = PmlOperator and P = PmlParamTerm

  type val_ = abt
  type cmp = abt

  type addr = Abt.metavariable
  type 'a closure = ('a, 'a) Cl.closure
  datatype 'a slot = HOLE | DONE of 'a | AWAIT of 'a closure
  type 'a frame = 'a slot appview
  type 'a stack = 'a frame list

  datatype cfg = 
     <| of cmp closure * cmp stack
   | |> of val_ closure * cmp stack

  fun @@ (f, x) = f x

  infix @@
  infix 3 <| |> <: `$ $ $$ \

  fun sym {params,terms} a =
    let
      val P.VAR a' = Sym.Ctx.lookup params a handle _ => P.VAR a
    in
      a'
    end

  fun init m = 
    m <: {params = Sym.Ctx.empty, terms = Var.Ctx.empty} 
      <| []

  fun down (m, env, stk) =
    case out m of
       ` x => SOME @@ Var.Ctx.lookup (#terms env) x <| stk
     | O.PAIR $ [_ \ m1, _ \ m2] =>
         SOME @@ m1 <: env <| (O.PAIR `$ [([],[]) \ HOLE, ([],[]) \ AWAIT (m2 <: env)]) :: stk
     | O.INL $ [_ \ m] => 
         SOME @@ m <: env <| (O.INL `$ [([],[]) \ HOLE]) :: stk
     | O.INR $ [_ \ m] => 
         SOME @@ m <: env <| (O.INL `$ [([],[]) \ HOLE]) :: stk
     | O.LAM $ _ => 
         SOME @@ m <: env |> stk
     | O.ABS $ [([a],[]) \ m] =>
         SOME @@ m <: env |> (O.ABS `$ [([a],[]) \ HOLE]) :: stk
     | O.NU $ [([a],[]) \ m] => 
         SOME @@ m <: env |> (O.NU `$ [([a],[]) \ HOLE]) :: stk
     | O.SWAP (a, b) $ [_ \ m] => 
         SOME @@ m <: env |> (O.SWAP (a, b) `$ [([],[]) \ HOLE]) :: stk

  fun up (v, env : abt closure Cl.env, stk) =
    case (out v, stk) of
       (_, []) => NONE
     | (_, (O.PAIR `$ [_ \ HOLE, _ \ AWAIT mcl]) :: stk) => 
         SOME @@ mcl <| (O.PAIR `$ [([],[]) \ DONE v, ([],[]) \ HOLE]) :: stk
     | (_, (O.PAIR `$ [_ \ DONE v1, _ \ HOLE]) :: stk) => 
         SOME @@ (O.PAIR $$ [([],[]) \ v1, ([],[]) \ v]) <: env |> stk
     | (_, (O.INL `$ [_ \ HOLE]) :: stk) =>
         SOME @@ (O.INL $$ [([],[]) \ v]) <: env |> stk
     | (_, (O.INR `$ [_ \ HOLE]) :: stk) =>
         SOME @@ (O.INR $$ [([],[]) \ v]) <: env |> stk
     | (_, (O.ABS `$ [([a],[]) \ HOLE]) :: stk) => 
         SOME @@ (O.ABS $$ [([a],[]) \ v]) <: env |> stk
     | (th $ es, (O.NU `$ [([a],[]) \ HOLE]) :: stk) => 
         let
           val supp = O.support th
         in
           if List.exists (fn (b,_) => Sym.eq (a, b)) supp then
             NONE
           else
             SOME @@ th $$ (List.map (fn bs \ m => bs \ (O.NU $$ [([a],[]) \ m])) es) <: env <| stk
         end
     | (th $ es, (O.SWAP (a, b) `$ [_ \ HOLE]) :: stk) =>
         let
           val a' = sym env a
           val b' = sym env b
           fun rho c = 
             let
               val c' = sym env c
             in
               if Sym.eq (c', a') then P.VAR b else if Sym.eq (c', b') then P.VAR a else P.VAR c
             end
           val th' = O.map rho th
           val es' = List.map (fn bs \ m => bs \ (O.SWAP (a, b) $$ [([],[]) \ m])) es
         in
           SOME @@ th' $$ es' <: env <| stk
         end

     | (O.LAM $ [([],[x]) \ mx], (O.AP `$ [_ \ HOLE, _ \ AWAIT vcl]) :: stk) =>
         SOME @@ mx <: insertVar env x vcl <| stk
     | (O.TT $ _, (O.PM O.PAT_ONE `$ [_ \ HOLE, _ \ AWAIT mcl]) :: stk) =>
         SOME @@ mcl <| stk
     | (O.PAIR $ [_ \ v1, _ \ v2], (O.PM O.PAT_TENSOR `$ [_ \ HOLE, ([], [x1,x2]) \ AWAIT (m <: envm)]) :: stk) =>
         SOME @@ m <: insertVar (insertVar envm x1 (v1 <: env)) x2 (v2 <: env) <| stk
     | (O.INL $ [_ \ v], (O.PM O.PAT_PLUS `$ [_ \ HOLE, ([],[x]) \ AWAIT (m <: envm), _]) :: stk) =>
         SOME @@ m <: insertVar envm x (v <: env) <| stk
     | (O.INR $ [_ \ v], (O.PM O.PAT_PLUS `$ [_ \ HOLE, _, ([],[x]) \ AWAIT (m <: envm)]) :: stk) =>
         SOME @@ m <: insertVar envm x (v <: env) <| stk

  
  val step = 
    fn m <: env <| stk => down (m, env, stk)
     | v <: env |> stk => up (v, env, stk)
end