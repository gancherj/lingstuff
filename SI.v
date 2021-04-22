
Require Import String. Import StringSyntax.
From Ling Require Import BS.
Import Ling.

(* John scratched his arm, and bob did too *)

(* An analysis of sloppy identity that's similar to the covariance one *)

(* TODO fix this *)

Definition scratched : TV := mkTV "scratched".

Parameter Of : DP -> DP -> DP.

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

Definition his : (DP >> S) || S -- (DP / DP) :=
  (fun k x => k (fun y => Of x y)).

Definition arm : DP := Ec "arm".

Definition john_scratched_his_arm :=
  lower (bind (lift john) |> (lift scratched <| (his <| lift arm))).

Eval compute in john_scratched_his_arm.

Definition did_too : ((DP \ S) >> S) || S -- (DP \ S) := fun k => k.

Definition bob : DP := baseE "bob".

(* Strict reading *)
Eval compute in
    (lower
            (bind (lift john) |>
             gbind (lift scratched <| (his <| lift arm)) |>
             (lift and <|
                   (lift bob |> did_too)))).


(* Scratched his arm as an intransitive VP *)
(* TODO: how to derive? *)
Definition scratched_his_arm' : S || S -- (DP \ S) :=
  (fun k => k (fun x => baseVP "scratched" (Of x (baseE "arm")) x)).

(* Sloppy reading *)
Eval compute in (lower ((lift john |> gbind (scratched_his_arm')) |> (lift and <| (lift bob |> did_too)))).




Definition gap {a b : Cat} : (a \\ b) || b -- a := fun x => x.

(* Maybe with gaps, to introduce abstraction *)
(* Gaps = hypothetical reasoning *)

Definition cleft_gap {a b c x y : Cat}
           (f : a || b -- x)
           (g : b || c -- (x \\ y)) : a || c -- y :=
  (fun k => f (fun x => g (fun y => k (y x)))).

Definition cright_gap {a b c x y : Cat} (f : a || b -- (x // y)) (g : b || c -- y) : a || c -- x :=
    (fun k => f (fun x => g (fun y => k (x y)))).

Notation "x |g> y" := (cleft_gap x y) (at level 41).
Notation "x <g| y" := (cright_gap x y) (at level 41).


Definition john_scratched_his_arm' : S || ((DP \\ S) >> S) -- S :=
  (lift john |g> (gbind (lift (lower (bind gap |> (lift scratched <| (his <| lift arm))))))).

Definition did_too_gap : ((DP \\ S) >> S) || S -- (DP \\ S) := fun k => k.

(*
        1. Remember "HOLE scratched his arm"
        2. Apply John to the above sentence
        3. Apply bob to the above sentence
*)

(* Sloppy reading, redux *)
Eval compute in (lower (john_scratched_his_arm' |>
                        (lift and <| (lift bob |g> did_too_gap)))).

