Require Import sniper.
From MetaCoq Require Import All.

Ltac metacoq_get_value p :=
  let id := fresh in
  let _ := match goal with _ => run_template_program p
  (fun t => pose (id := t)) end in
  let x := eval cbv delta [id] in id in
  let _ := match goal with _ => clear id end in
  x.
Print kername.

MetaCoq Quote Definition bool_reif := bool.
Print bool_reif.

Lemma n : nat.
exact 0.
Qed.

Goal True.
let x := metacoq_get_value (tmQuoteRec bool) in idtac x.
let x := metacoq_get_value (tmQuote bool) in idtac x.
let x := metacoq_get_value (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Coq"], "bool")) in idtac x. 
(* let x := metacoq_get_value (tmQuoteConstant "n" true) in idtac x.
let x := metacoq_get_value (tmQuoteConstant "n" false) in idtac x. *)
let x := metacoq_get_value (tmQuote 0) in let y := metacoq_get_value (tmUnquote x) in idtac y.
let x := metacoq_get_value (tmQuote 0) in let y := metacoq_get_value (tmUnquoteTyped nat x) in idtac y.
Abort.

Print lookup_env.
Print Ast.

MetaCoq Quote Definition nat_reif := nat.

Print nat_reif.


Definition get_nb_constructors i Σ := 
match i with 
| tInd indu _ => match lookup_env Σ indu.(inductive_mind) with
                | Some (InductiveDecl decl) => match ind_bodies decl with 
                          | nil => 0
                          | x :: _ => length (ind_ctors x)
                          end
                | _ => 0
end
| _ => 0
end.

MetaCoq Quote Recursively Definition list_reif_rec := list.

Compute get_nb_constructors list_reif_rec.2 list_reif_rec.1.



(* Ltac get_nb_constructors_tac i k :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => 
k constr:(get_nb_constructors i_reif_rec.2 i_reif_rec.1)). *)

Ltac get_nb_constructors_tac i id :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => let n := 
eval cbv in (get_nb_constructors i_reif_rec.2 i_reif_rec.1) in
pose (id := n)).

(* NOTE : il faut donner en paramètre de la continuation une vraie tactique c'est à dire une pas 
value_tactic *)


Goal True.
get_nb_constructors_tac bool ident:(foo).
exact I. Qed.


Goal False.
let H := fresh in get_nb_constructors_tac bool H.
Abort.


Ltac create_evars_for_each_constructor i := 
let y := metacoq_get_value (tmQuoteRec i) in 
let n:= eval cbv in (get_nb_constructors y.2 y.1) in
let rec tac_rec u := match constr:(u) with 
      | 0 => idtac
      | S ?m => let H' := fresh in let H'_evar := fresh H' in epose (H' := ?[H'_evar] : Prop) ; tac_rec m
end in tac_rec n.

Goal True.

create_evars_for_each_constructor bool.
create_evars_for_each_constructor unit.
create_evars_for_each_constructor nat.
Abort.

Lemma dummy_length : forall A (l : list A), length l = match l with | nil => 0 | cons x xs => S (length xs) end.
intros. destruct l; simpl;  reflexivity. Qed.

Lemma test_match: (False -> forall A (l : list A), length l = match l with | nil => 0 | cons x xs => S (length xs) end) 
/\ True.
Proof. create_evars_for_each_constructor list. split.
intros Hfalse A l. case l; try clear l; revert A; 
match goal with 
| u : Prop |- ?G => instantiate (u := G) ; destruct Hfalse end.
repeat match goal with 
| u : Prop |-_ => let u' := eval unfold u in u in assert u' by ( intros; apply dummy_length) ; clear u end.
exact I. 
Qed. 
 


Ltac create_evars_and_inst_rec n l := 
match constr:(n) with 
| 0 => l
| S ?m => let H := fresh in 
let H_evar := fresh in 
let _ := match goal with _ => epose (H := ?[H_evar] : nat) end in 
create_evars_and_inst_rec m constr:(H :: l) end.




Goal True.

let l:= (create_evars_and_inst_rec 4 (@nil nat)) in pose l. (* comportement super bizarre quand on enlève le repeat *) 

Ltac create_evars_and_inst n := 
create_evars_and_inst_rec n (@nil nat).


let l:= (create_evars_and_inst 4) in pose l. (* comportement super bizarre quand on enlève le repeat *)
exact I. 


Ltac eliminate_pattern_matching H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) ; let T := type of x in 
let y := metacoq_get_value (tmQuoteRec T) in 
let nconst:= eval cbv in (get_nb_constructors y.2 y.1) in
let rec tac_rec_constr u := match constr:(u) with 
      | 0 => idtac
      | S ?m => let H' := fresh in let H'_evar := fresh H' in epose (H' := ?[H'_evar] : Prop) ; tac_rec_constr m
end in tac_rec nconst
                                    end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct_applied A n) in 
let l_ctor_and_ty_ctor := eval cbv in (combine l_ctors l_ty_ctors) in
let list_of_hyp := eval cbv in (get_equalities E l_ctor_and_ty_ctor l) in
 unquote_list list_of_hyp ; prove_hypothesis H )] ; clear H.