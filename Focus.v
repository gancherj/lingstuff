
Require Import String. Import StringSyntax.
From Ling Require Import BS.
Import Ling.

Notation "x [ y ]" := (Focus y x) (at level 30, format "x [ y ]").

(* BOUGHT : capture the continuation, return the continuation along with the word *)

(* This version of focus doesn't work for phrases. Like 
    "I only GAVE IT TO MARY"
   meaning
     the only thing I did is "give it to mary"
    
   but maybe this is ok
*)
Definition focus {a b : Cat} (x : b) : a[b] || a -- b := fun (k : b -> a) => (x, k).


Definition only {c d : Cat} : S || S[c] -- (d / d) :=
  fun F => let '(x, k) := F id in forall z, k z -> z = x.

(* John bought lunch. *)
Check john.
Definition bought := mkTV "bought".
Definition lunch : DP := Ec "lunch".
Eval compute in (john <: (bought :> lunch)).

Eval compute in (lower (lift john <| (lift bought |> lift lunch))).

(* John only BOUGHT lunch *)

Eval compute in (lower (lift john <| ((only |> focus bought) |> lift lunch))).

(* John bought only LUNCH *)

Eval compute in (lower (lift john <| (lift bought |> (only |> focus lunch)))).

(* only JOHN bought lunch *)

Eval compute in (lower ((only |> focus john) <| (lift bought |> lift lunch))).

