
Require Import String. Import StringSyntax.          

From Ling Require Import BS. 
Import Ling.

(* muddy, copulatives *)

Definition muddy : AP := ET "muddy".
Definition is : (DP \ S) / AP := fun x y => x y.
 

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

Notation "x [ y ]" := (Focus y x) (at level 30, format "x [ y ]").

Definition bought := mkTV "bought".
Definition lunch : DP := Ec "lunch".
Definition alice : DP := Ec "alice".
Definition focus (x : DP) : DP[DP] := (x, id).

Definition fextract {a b c d : Cat} (x : a || b -- (c[d])) : a || b -- c := fmap (fun (s : c[d]) => (snd s) (fst s)) x.

Definition fappf {a b c : Cat} (y : a / b) (x : b[c]) : a[c] :=
  (fst x, fun a => y (snd x a)).
Definition fappb {a b c : Cat} (x : b[c]) (y : b \ a) : a[c] := 
  (fst x, fun a => y (snd x a)).

Notation "x :f> y" := (fappf x y) (at level 40).
Notation "x <f: y" := (fappb x y) (at level 40).

Definition contrast {a} (f : S || S -- (S[a])) : (S[a] >> S) || S -- S := (fun k old => k (f (fun new => (snd new) (fst new) /\ (snd new) = (snd old) /\ (fst new) <> (fst old)))).

Definition ALICE_bought_lunch : S || (S[DP] >> S) -- S := 
    fextract (gbind (lift (focus alice <f: (bought :> lunch)))).

Definition JOHN_bought_lunch := 
    contrast (lift (focus john <f: (bought :> lunch))).


Eval compute in (lower (ALICE_bought_lunch <| (lift and |> JOHN_bought_lunch))).





(* How is this related to focus? *)

Definition only {b : Cat} (x : b) : S || S -- (b).
  simpl.
  refine (fun k => k x /\ forall z, k z -> z = x).
Defined.

Eval compute in (lower (only john <| (lift (bought :> lunch)))).
