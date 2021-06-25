

Require Import String. Import StringSyntax.          
From Ling Require Import BSm2. 
Import Ling.
From Ling Require Import Parasitic.
From Ling Require Import Covariance.


(* John scratched his arm, and bob did too *)

(* An analysis of sloppy identity that's similar to the covariance one *)

Definition scratched : TV := mkTV "scratched".

Parameter Of : DP -> DP -> DP.


Definition his : (DP >> S) || S -- (DP / DP) :=
  (fun k x => k (fun y => Of x y)).

Definition arm : DP := e "arm".
Definition bob : DP := e "bob".

(* strict reading *)
Eval compute in (lower ((lower (bind (lift john) <| ant1 (lift scratched |> (his |> lift arm))))
         <| (lift and |> (FOC bob <| did)))).


(* sloppy reading *)

Eval compute in (lower ((lower (lift john <| (ant0 (fill_dp (lift scratched |> (his |> lift arm)))))) <| (lift and |> (FOC bob <| did)))).


