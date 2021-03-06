 
Require Import String. Import StringSyntax.          
From Ling Require Import BSm2. 
Import Ling.
From Ling Require Import Parasitic.


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

Definition knows : ((DP \ S) / S) := Knows. 

Check ant.
Check (lift knows |> (he <| (lift is |> lift muddy))).

Definition gap : (DP >> S) || (DP >> S) -- DP.
  intros k x.
  apply (k x x).
Defined.

(* c : (DP \ S) -> S *)
(* k : S -> (S[DP \ S] >> S) *)

(* First attempt, down't work out. *)
Definition ant_bad (f : (DP >> S) || S -- (DP \ S)) :
  ((DP >> S) || (S[DP \ S] >> S) -- S) || S -- (DP \ S).
  intros c k X.
  apply (f (fun v => k (c v) (v, c)) X).
Defined.

(* The DP >> _ part is too high in the tower to bind easily. *)
Check (ant_bad (lift knows |> (he <| (lift is |> lift muddy)))).



(* ant with towers, one variable *)
Definition ant1 (f : (DP >> S) || S -- (DP \ S)) :
  (DP >> (S || (S[DP \ S] >> S) -- S)) || S -- (DP \ S).
  intros k x K.
  refine (f (fun v => K (k v) (v, k)) x).
Defined.

(* This version lowers the DP >> _ part to the ordinary binding position. *)
Check (ant1 (lift knows |> (he <| (lift is |> lift muddy)))).


(* invariant *)
Eval compute in (lower (lower (bind (lift ari) <| ant1 (lift knows |> (he <| (lift is |> lift muddy)))) <| (lift and |> (FOC alice <| did)))).


(* *** covariant  *** *)


(* We need a combinator that turns "knows he is muddy" into a simple (DP \ S), without any binding. *) 

Definition fill_dp (f : (DP >> S) || S -- (DP \ S)) : S || S -- (DP \ S).
  intro k.
  simpl in *.
  apply (k (fun x => f (fun v => v x) x)).
Defined.

(* same as ant1, but no variables *)
Definition ant0 (f : S || S -- (DP \ S)) :
  ((S || (S[DP \ S] >> S) -- S)) || S -- (DP \ S).
  intros k K.
  refine (f (fun v => K (k v) (v, k))).
Defined.

Eval compute in  (lower (lower (lift ari <| (ant0 (fill_dp (lift knows |> (he <| (lift is |> lift muddy)))))) <| (lift and |> (FOC alice <| did)))).




(** ****   *)

(* two variables *)
Definition ant2 (f : (DP >> (DP >> S)) || S -- (DP \ S)) :
  (DP >> (DP >> (S || (S[DP \ S] >> S) -- S))) || S -- (DP \ S).
  intros k x y K.
  apply (f (fun v => K (k v) (v, k)) x y).
Defined.

(* three variables *)
Definition ant3 (f : (DP >> (DP >> (DP >> S))) || S -- (DP \ S)) :
  (DP >> (DP >> (DP >> (S || (S[DP \ S] >> S) -- S)))) || S -- (DP \ S).
  intros k x y z K.
  apply (f (fun v => K (k v) (v, k)) x y z).
Defined.




