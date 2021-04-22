 
Require Import String. Import StringSyntax.          

(*
Add LoadPath  "/local/res/josh/coq" as Ling. *)

Add LoadPath  "/local/res/josh/coq" as Ling.

(*
As you can see there are this first line in any source files Require Import Bool Arith List Cpdt.CpdtTactics.
Add LoadPath "CODEHOME/cpdt/src" as Cpdt .
*)

(* First
 /Applications/CoqIDE_8.13.1.app/Contents/Resources/bin/coqc -Q . Ling -vos BSm.v 
*)

From Ling Require Import BSm. 

Import Ling.

(**** Some experimentation with gaps, covariant readings  *****)
(*** Everything below here is pretty experimental ***)


(* Gap is defined for all input and output categories *)
Definition gap {a b : Cat} : (a \\ b) || b -- a := fun x => x.

(* Simple gaps *)
Eval compute in (lower (lift john <| (lift loves |> gap))).


(* Ari knows he is muddy and Ben knows this *)

(* muddy, copulatives *)

Definition muddy : AP := ET "muddy".
Definition is : (DP \ S) / AP := fun x y => x y.
Eval compute in (lower (lift john <| (lift is |> lift muddy))).

(* alternatively *)
Eval compute in john <: (is :>  muddy).

Definition knows : ((DP \ S) / S) := ((fun p => (fun x => know x p)) : (DP \ S) / S).

Check (bind (lift john) <| (lift knows |> (he <| (lift is |> lift muddy)))).

(* alternatively *)

Check (lower (bind (lift john) <| (lift knows |> (he <| lift (is :> muddy))))).
Eval compute in (lower (bind (lift john) <| (lift knows |> (he <| lift (is :> muddy))))).

(* It comes out as 
  know (Ec "john") (ET "muddy" (Ec "john")) : S   *)

(* Anaphor for single props *)
Definition this : (S >> S) || S -- S := fun k => k.

(* Assumes a topic DP and a proposition P with a hole in it for a DP. Applies
   P to the topic. *)
Definition this2 : (DP >> ((DP >> S) >> S)) || S -- S.
  simpl.
  refine (fun k e p => k (p e)).
Defined.

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

(* The anaphor this2 has a hole, which (bind (lift mary)) captures. *)

Check (bind (lift mary) <| (lift knows |> this2)).
(*
((DP >> S) >> S) || S
--
S
*)


Check (gbind (lift ((lower (he <| (lift is |> lift muddy)))))).



(* This pull combinator is kind of suspect. Maybe I can fix it with gaps *)
Definition pull {a b c d : Cat} (x : a || b -- (c >> d)) : (c >> a) || b -- d :=
  fun k z => x (fun f => k (f z)).

Definition ari : DP := Ec "ari".
Definition ben : DP := Ec "ben".

Check ((lower (he <| (lift is |> lift muddy)))).
Definition ari_knows_he_is_muddy : S || (DP >> S) >> S -- S := (bind (lift ari) <| (lift knows |> (pull (gbind (lift ((lower (he <| (lift is |> lift muddy))))))))).

Definition doesnt_know : ((DP \ S) / S) := fun x k => ~ (know k x).

Definition ben_doesnt_know_this : ((DP >> S) >> S) || S -- S :=
  (bind (lift ben) <| (lift doesnt_know |> this2)).
  
Eval compute in (lower (ari_knows_he_is_muddy <| (lift and |> ben_doesnt_know_this))).
