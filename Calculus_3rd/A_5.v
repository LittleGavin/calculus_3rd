Require Import A_4.
Require Import Classical.


(*微积分系统的基本定理*)


(* 定理4.1: 设F(x)在[a,b]上一致可导，其导数为f(x).
   若在[a,b]上恒有f(x)>=0, 则F(x)单调增；
   若在[a,b]上恒有f(x)<=0, 则F(x)单调减；
   不等式中等号不成立时，则F(x)严格单调增或严格单调减 *)

Theorem th5_1 : forall F f a b, derivative F f a b -> 
  ((forall x, x ∈ [a,b] -> f(x)>=0) -> mon_increasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)<=0) -> mon_decreasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)>0) -> strict_mon_increasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)<0) -> strict_mon_decreasing F [a,b]).
Proof.
  intros.
  apply th4_4 in H.
  destruct H.
  unfold diff_quo_median in H.
  repeat split; intros.
  - unfold mon_increasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x0 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H2, H3, H4; unfold cc in H2, H3, H4.
       destruct H2, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rle_trans with (r1:=0) in H7.
    apply Rmult_le_compat_r with (r:= y-x) in H7.
    rewrite Rmult_0_l in H7.
    unfold Rdiv in H7; rewrite Rinv_mult_rgt0 in H7; auto.
    apply Rplus_le_reg_r with (r:=-F x). rewrite Rplus_opp_r; auto.
    apply Rlt_le; auto.
    apply Rge_le; auto.
  - unfold mon_decreasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x1 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H6, H3, H4; unfold cc in H6, H3, H4.
       destruct H6, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rle_trans with (r3:=0) in H8; auto.
    apply Rmult_le_compat_r with (r:= y-x) in H8.
    rewrite Rmult_0_l in H8.
    unfold Rdiv in H8; rewrite Rinv_mult_rgt0 in H8; auto.
    apply Rle_ge; apply Rplus_le_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto.
    apply Rlt_le; auto.
  - unfold strict_mon_increasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x0 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H2, H3, H4; unfold cc in H2, H3, H4.
       destruct H2, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rlt_le_trans with (r1:=0) in H7; auto.
    apply Rmult_lt_compat_r with (r:= y-x) in H7; auto.
    rewrite Rmult_0_l in H7.
    unfold Rdiv in H7; rewrite Rinv_mult_rgt0 in H7; auto.
    apply Rplus_lt_reg_r with (r:=-F x). rewrite Rplus_opp_r; auto.
  - unfold strict_mon_decreasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x1 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H6, H3, H4; unfold cc in H6, H3, H4.
       destruct H6, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rle_lt_trans with (r3:=0) in H8; auto.
    apply Rmult_lt_compat_r with (r:= y-x) in H8; auto.
    rewrite Rmult_0_l in H8.
    unfold Rdiv in H8; rewrite Rinv_mult_rgt0 in H8; auto.
    apply Rplus_lt_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto.
Qed.

(* Parameter  definite_integral : (R->R)->R->R->R.

Axiom def_integral : forall F f a b , derivative F f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] -> definite_integral f u v = F v - F u.

(*定理4.2*)
Theorem th4_2 : forall F f a b , derivative F f a b ->
  integ_sys (definite_integral f) f a b.
Proof.
  intros.
  generalize H; intro.
  apply th4_4 in H.
  destruct H.
  apply th3_1_2 with(S:=(definite_integral f)) in H; try tauto.
  intros.
  apply def_integral with(a:=a)(b:=b); auto.
Qed.


Definition def_integral' (F: R->R) := fun u v => F v - F u.  *)
Theorem th5_2 : forall F f a b , derivative F f a b ->
  integ_sys (fun a b => F b - F a) f a b.
Proof.
  intros.
  apply th4_4 in H.
  destruct H.
  apply th4_1_2 with(S:=(fun a b => F b - F a)) in H; try tauto.
Qed.

Theorem th5_3 : forall G f a b, uniform_continuous f a b ->
  (exists (S: R->R->R), integ_sys' S f a b /\
  forall x, x ∈ [a,b] -> G(x) = S a x) ->
  derivative G f a b.
Proof.
  intros.
  destruct H0, H0. rename x into S.
  assert(diff_quo_median G f a b).
   { unfold diff_quo_median.
     intros.
     unfold integ_sys' in H0.
     destruct H0.
     unfold additivity' in H0.
     unfold median in H3.
     assert(a ∈ [a, b] /\ u ∈ [a, b] /\ v ∈ [a, b]).
      { split; try tauto.
        unfold In; unfold cc.
        destruct H2.
        unfold In in H2; unfold cc in H2; destruct H2.
        split; auto.
        split. apply Req_le; reflexivity.
        apply Rlt_le; auto. }
     apply H0 in H4.
     generalize (H1 u); intro.
     generalize (H1 v); intro.
     rewrite H5; try tauto. clear H5.
     rewrite H6; try tauto. clear H6.
     assert(v - u > 0) as gt_v_u . { tauto. }
     apply H3 in H2. destruct H2, H2, H2, H5.
     exists x,x0.
     split; auto. split; auto.
     apply Rmult_le_r with(r:=v-u); auto.
     rewrite Rplus_comm in H4; rewrite <- H4.
     unfold Rminus. rewrite Rplus_assoc.
     rewrite Rplus_opp_r; rewrite Rplus_0_r.
     unfold Rdiv. rewrite Rinv_mult_rgt0; auto. }
  apply th4_4.
  split; auto.
Qed.


(* Taylor公式的预备定理 *)

(* 若H在[a,b]上n阶一致(强)可导（n为正整数），且有
    (1) 在[a,b]上有..... *)

Parameter F' : (R->R)->nat->R->R.

Axiom N_uniform_str_derivative : forall F a b (N:nat),
  (N>=1)%nat -> str_derivative F (F' F (S N)) a b ->
  str_derivative (F' F (S N)) (F' F N) a b.

(*N阶强可导*)
Fixpoint N_Uniform_str_derivability F a b (n:nat) : Prop :=
  match n with
  | 0 => False
  | 1 => str_derivative F (F' F 1) a b
  | S p =>  str_derivative F (F' F (S p)) a b /\
                   N_Uniform_str_derivability (F' F (S p)) a b p
  end.

(*
  阶乘：
    factorial 0 = 1
    factorial 5 = 5*4*3*2*1
*)
Fixpoint  factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S p => S p * (factorial p)
  end.


(* Compute (factorial 0). *)
(* Compute (factorial 5). *)

(* n次方:
    power_n 0 2 = 1
    power_n 5 2 = 2*2*2*2*2
*)
Fixpoint  power_n (n:nat) x : R :=
  match n with
  | 0 => 1
  | S p => x * power_n p x
  end.
  
(* Compute (power_n 0 10). *)
(* Compute (power_n 5 10). *)

(*
  ∑

*)
Fixpoint something_toname x1 x2 (n i:nat) : R :=
  match i with
  | 0 => power_n n x1
  | S p => (power_n (n - S p) x1)*(power_n (S p) x2) + something_toname x1 x2 n p
  end.


(* Variable x1 x2:R.

Compute (factorial 8).
Compute (power_n 3 x1).
Compute (something_toname x1 x2 4 3).
Compute (something_toname x1 x2 3 3). *)


Lemma fix_property : forall x y (n i:nat), (i<=n)%nat ->
  something_toname x y (n+1) i = x*something_toname x y n i.
Proof.
  intros.
  assert(forall x (n:nat), x * power_n n x = power_n (n + 1) x).
     { intros.
       induction n0; simpl; auto.
       rewrite IHn0; auto. }
  induction i.
  - simpl.
    rewrite H0; auto.
  - simpl.
    generalize H; intro.
    apply le_Sn_le in H.
    rewrite (IHi H); rewrite Rmult_plus_distr_l.
    apply Rplus_eq_compat_r.
    rewrite <- (Rmult_assoc x); rewrite (H0 x).
    rewrite Nat.add_sub_swap; auto.
Qed.


(*
  分解定理：
  x^(n+1) - y^(n+1) = (x-y)*∑(x^(n-i)*y^i)
*)
Lemma  fenjie : forall x y (n:nat),
  power_n (n+1) x - power_n (n+1) y = (x-y)*something_toname x y n n.
Proof.
  intros.
  induction n.
  - simpl.
    repeat rewrite Rmult_1_r; auto.
  - simpl.
    rewrite <- (Nat.add_1_r n).
    rewrite (fix_property x y n n); auto.
    rewrite Nat.sub_diag.
    simpl. rewrite Rmult_1_l.
    rewrite (Rmult_plus_distr_l (x-y) (y * power_n n y) (x * something_toname x y n n)).
    rewrite Rmult_comm with (r2:=(x * something_toname x y n n)).
    rewrite Rmult_assoc with (r1:=x).
    rewrite Rmult_comm with (r1:=something_toname x y n n).
    rewrite <- IHn.
    rewrite Rplus_comm.
    unfold Rminus. rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_l.
    rewrite Rplus_assoc; apply Rplus_eq_compat_l.
    rewrite <- Rplus_assoc.
    assert(forall x (n:nat), x * power_n n x = power_n (n + 1) x).
     { intros.
       induction n0; simpl; auto.
       rewrite IHn0; auto. }
    assert(x * - power_n (n + 1) y + x * (y * power_n n y) = 0).
     { rewrite <- Rmult_plus_distr_l.
       rewrite H; ring. }
    rewrite H0; rewrite Rplus_0_l.
    rewrite (H y n). ring.
Qed.


Lemma exist_Rgt_lt : forall r1 r2,r1<r2 -> exists r, r1<r<r2.
Proof.
Admitted.

Lemma Taylor_Lemma : forall H a b (n:nat), (n>0)%nat ->
  N_Uniform_str_derivability H a b n ->
  (forall k, (k<n)%nat -> F' H k a = 0 /\ F' H 0  = H ) ->
  forall m M, (forall x, x ∈ [a,b] ->  m <= F' H n x <= M) ->
  forall x, x ∈ [a,b] ->
  m*power_n n (x-a)/INR (factorial n) <= H x <= M*power_n n (x-a)/ INR(factorial n).
Proof.
  intros.
  induction n.
  apply Nat.lt_neq in H0; contradiction.
  (*强可导可以推出一致可导*)
  assert(forall f, str_derivative H f a b -> derivative H f a b ).
   { intros.
     unfold str_derivative in H5.
     unfold derivative.
     exists (fun x => x).
     split.
     - unfold pos_inc.
       split; intros.
       unfold In in H6; unfold oc in H6; tauto.
       apply Rlt_le; auto.
     - split. 
       + unfold bounded_rec_f; intros.
         assert(exists z : R, z ∈ (0, b - a] /\ z < 1/M0).
          { assert(0<b-a).
             { unfold In in H4; unfold cc in H4.
               destruct H4. apply Rlt_Rminus; auto. }
            generalize (total_order_T (1/M0) (b-a)); intro.
            destruct H8. destruct s.
            - generalize(exist_Rgt_lt 0 (1/M0)); intro.
              destruct H8.
              unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; auto.
              exists x0. unfold In; unfold oc.
              destruct H8. repeat split; auto.
              apply Rlt_le; apply Rlt_trans with (r2:=1/M0); auto. 
            - apply Rinv_0_lt_compat in H6.
              apply exist_Rgt_lt in H6. destruct H6, H6.
              exists x0. unfold In; unfold oc.
              repeat split; auto. rewrite <- e; apply Rlt_le.
              unfold Rdiv; rewrite Rmult_1_l; auto.
              unfold Rdiv; rewrite Rmult_1_l; auto.
            - generalize H7; auto.
              apply exist_Rgt_lt in H7. destruct H7, H7.
              exists x0. unfold In; unfold oc.
              repeat split; auto. apply Rlt_le; auto.
              apply Rlt_trans with (r2:=b-a); auto. }
        destruct H7, H7.
        exists x0. split; auto.
        unfold In in H7; unfold oc in H7.
        destruct H7, H9.
        rewrite Rabs_right. unfold Rdiv; rewrite Rmult_1_l.
        unfold Rdiv in H8; rewrite Rmult_1_l in H8.
        apply Rinv_lt_contravar in H8.
        rewrite Rinv_involutive in H8; auto.
        apply Rgt_not_eq; auto.
        apply Rmult_lt_0_compat; auto.
        apply Rinv_0_lt_compat; auto.
        unfold Rdiv; rewrite Rmult_1_l; apply Rgt_ge.
        apply Rlt_gt; apply Rinv_0_lt_compat; auto.
      + destruct H5, H5. exists x0. split; auto.
        intros.
        rewrite Rmult_assoc; rewrite <- Rabs_mult.
        rewrite (Rabs_pos_eq (h*h)).
        simpl in H6.
        rewrite <- (Rmult_1_r (h * h)); rewrite Rmult_assoc.
        apply H6; tauto.
        apply Rlt_le; apply Rsqr_pos_lt; tauto. }
  generalize (Nat.le_0_l n) as le_n_0; intro.
  destruct le_n_0.
  (*证明n=0时满足*)
  - simpl in H1.
    apply H5 in H1; apply th4_4 in H1.
    destruct H1. clear H6.
    unfold diff_quo_median in H1.
    simpl. unfold Rdiv; rewrite Rinv_1; repeat rewrite Rmult_1_r.
    unfold In in H4; unfold cc in H4. destruct H4, H6, H6.
    
    (*差商中值 存在pq*)
    + destruct (H1 a x).
      unfold In; unfold cc.
      repeat split; auto.
      apply Rge_refl. apply Rlt_le; auto. apply Rlt_le; tauto.
      apply Rgt_minus; tauto.
      destruct H8, H8, H9.
      apply H2 in H0; destruct H0. rewrite H11 in H0; rewrite H0 in H10.
      rewrite Rminus_0_r in H10.
      apply (Rmult_le_r (/(x-a))). apply Rinv_0_lt_compat. apply Rlt_Rminus; auto.
      assert(x-a<>0). { apply Rgt_not_eq. apply Rgt_minus; auto. }
      repeat rewrite Rinv_r_simpl_l; auto.
      destruct H10.
      assert(forall x0, x0 ∈ [a, x] -> x0 ∈ [a, b]).
       { intros. unfold In; unfold cc.
        unfold In in H14; unfold cc in H14.
        destruct H14, H15.
        repeat split; auto. apply Rle_trans with (r2:=x); auto. }

      apply H14 in H8; apply H14 in H9.
      apply H3 in H8; apply H3 in H9.
      destruct H8, H9. unfold Rdiv in H10, H13.
      split. apply Rle_trans with(r2:=F' H 1 x0); auto.
      apply Rle_trans with (r2:=F' H 1 x1); auto.
    + apply H2 in H0. destruct H0.
      rewrite H8 in H0; rewrite <- H6; rewrite H0.
      rewrite Rminus_diag_eq; auto. repeat rewrite Rmult_0_r.
      split; apply Rle_refl.
  (*证明n>0时成立*)
  - rename m0 into n.
    generalize (gt_Sn_O n); intro. apply IHn in H6; auto.
    simpl in H1.
    2: simpl; auto.
    destruct H1.
    simpl in H6.
    simpl.
    Admitted.

(* Theorem th4_4 : forall F a b n, N_Uniform_str_derivability F a b (n:nat),
  forall k:nat, k<=n-1 ->  *)











































