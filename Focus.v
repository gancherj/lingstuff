 
Require Import String. Import StringSyntax.          

From Ling Require Import BS. 
Import Ling.

(* muddy, copulatives *)

Definition muddy : AP := ET "muddy".
Definition is : (DP \ S) / AP := fun x y => x y.
 

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

(* Individuals *)
Definition ari : DP := Ec "ari".
Definition ben : DP := Ec "ben".

(* Presupposition of focus.  In alt(p,Q,x), p is the contrasting proposition,
 x is the semantics of the focused phrase, and Q is an abstract binding a variable
 in the position of the focused phrase in the scope of the focus. 
 It adds a presupposition that p is obtainable by applying Q to something
 other than x. *)
 
(* Relies on intensional equality in Coq. Invalid under proof irrelevance. *)
Definition alt : Prop -> ((interp DP) -> Prop) -> interp DP -> Prop :=
  fun p Q x =>
    (exists y,  p = Q y) /\ (p <> Q x).

(* Focusing operator.  (focus ben) takes scope at the S (focus ben is muddy).
At that level, the tower result is ((S >> S) || S -- S), which is an S
with an unresolved proposition anaphor.  The antecedent is the contrasting
proposition. *)

Definition focus  {a : Cat} (x : DP) : ((S >> S) || S -- S)|| S -- DP :=
  fun k => (fun f => (fun p => (f (alt p k x)) /\ k x)).

(* Propositional anaphora is resolved with gbind. *)

Eval compute in lower ((gbind (lift (ari <: (is :> muddy)))) <| 
      ((lift and) |> (lower ((focus ben)  <| (lift (is :> muddy)))))).

Eval compute in
    (lower ((gbind (lift (ari <: (is :> muddy)))) <| ((lift and) |> (focus2 ben <| (lift (is :> muddy)))))).

(*
     =  ET "muddy" (Ec "ari") 
        /\ alt (ET "muddy" (Ec "ari")) (fun x : E => ET "muddy" x) (Ec "ben")
        /\ ET "muddy" (Ec "ben")
     : S

Ari is muddy, Ben is muddy, and the proposition 'Ari is muddy' is of the form
'y is muddy' and is distinct from 'Ben is muddy'.

*)

 



