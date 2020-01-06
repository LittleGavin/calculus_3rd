Require Import A_4.

(*微积分系统的基本定理*)


(* 定理4.1: 设F(x)在[a,b]上一致可导，其导数为f(x).
   若在[a,b]上恒有f(x)>=0, 则F(x)单调增；
   若在[a,b]上恒有f(x)<=0, 则F(x)单调减；
   不等式中等号不成立时，则F(x)严格单调增或严格单调减 *)

Theorem Theorem5_1 : forall F f a b, derivative F f a b -> 
  ((forall x, x ∈ [a,b] -> f(x)>=0) -> mon_increasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)<=0) -> mon_decreasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)>0) -> strict_mon_increasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)<0) -> strict_mon_decreasing F [a,b]).
Proof.
  intros.
  apply Theorem4_4 in H. destruct H.
  unfold diff_quo_median in H.
  assert(forall x0 x y a b, x0 ∈ [x, y] ->
         x ∈ [a, b] -> y ∈ [a, b] -> x0 ∈ [a, b]) as Domain_x0.
   { intros.
     destruct H1, H2, H3. split; auto. split.
     apply Rle_trans with (r2:=x); tauto.
     apply Rle_trans with (r2:=y); tauto. }
  repeat split; intros.
  - unfold mon_increasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4, H2, H2, H2, H6, H7.
    apply Domain_x0 with (x0:=x0)(x:=x) in H4; auto.
    apply H1 in H4.
    apply Rle_trans with (r1:=0) in H7.
    apply Rmult_le_compat_r with (r:= y-x) in H7.
    rewrite Rmult_0_l in H7.
    unfold Rdiv in H7; rewrite Rinv_mult_rgt0 in H7; auto.
    apply Rplus_le_reg_r with (r:=-F x). rewrite Rplus_opp_r; auto.
    apply Rlt_le; auto. apply Rge_le; auto.
  - unfold mon_decreasing; intros.
    generalize H2 as H3; intro. apply H in H2.
    destruct H3, H4, H2, H2, H2, H6, H7.
    apply Domain_x0 with (x0:=x1)(x:=x) in H4; auto.
    apply H1 in H4.
    apply Rle_trans with (r3:=0) in H8; auto.
    apply Rmult_le_compat_r with (r:= y-x) in H8.
    rewrite Rmult_0_l in H8.
    unfold Rdiv in H8; rewrite Rinv_mult_rgt0 in H8; auto.
    apply Rle_ge; apply Rplus_le_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto. apply Rlt_le; auto.
  - unfold strict_mon_increasing; intros.
    generalize H2 as H3; intro. apply H in H2.
    destruct H3, H4, H2, H2, H2, H6, H7.
    apply Domain_x0 with (x0:=x0)(x:=x) in H4; auto.
    apply H1 in H4.
    apply Rlt_le_trans with (r1:=0) in H7; auto.
    apply Rmult_lt_compat_r with (r:= y-x) in H7; auto.
    rewrite Rmult_0_l in H7.
    unfold Rdiv in H7; rewrite Rinv_mult_rgt0 in H7; auto.
    apply Rplus_lt_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto.
  - unfold strict_mon_decreasing; intros.
    generalize H2 as H3; intro. apply H in H2.
    destruct H3, H4, H2, H2, H2, H6, H7.
    apply Domain_x0 with (x0:=x1)(x:=x) in H4; auto.
    apply H1 in H4.
    apply Rle_lt_trans with (r3:=0) in H8; auto.
    apply Rmult_lt_compat_r with (r:= y-x) in H8; auto.
    rewrite Rmult_0_l in H8.
    unfold Rdiv in H8; rewrite Rinv_mult_rgt0 in H8; auto.
    apply Rplus_lt_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto.
Qed.




Theorem Theorem5_2 : forall F f a b , derivative F f a b ->
  (fun u v=>F v-F u) ∫ f (x)dx a b.
Proof.
  intros.
  apply Theorem4_4 in H.
  destruct H.
  apply Theorem4_2 in H; auto.
  destruct H; auto.
Qed.


Theorem Theorem5_3 : forall G f a b, uniform_continuous f a b ->
  (exists (S: R->R->R), integ_sys' S f a b /\
  forall x, x ∈ [a,b] -> G(x) = S a x) ->
  derivative G f a b.
Proof.
  intros.
  destruct H0, H0. rename x into S.
  assert(diff_quo_median G f a b).
   { unfold diff_quo_median. intros.
     unfold integ_sys' in H0. destruct H0.
     unfold additivity' in H0. unfold median in H3.
     assert(a ∈ [a, b] /\ u ∈ [a, b] /\ v ∈ [a, b]).
      { split; try tauto. destruct H2, H2.
        split; auto. split.
        apply Req_le; reflexivity.
        apply Rlt_le; auto. }
     apply H0 in H4.
     generalize (H1 u); intro.
     generalize (H1 v); intro.
     rewrite H5; try tauto. clear H5.
     rewrite H6; try tauto. clear H6.
     assert(v - u > 0) as gt_v_u . { tauto. }
     apply H3 in H2. destruct H2, H2, H2, H5.
     exists x,x0. split; auto. split; auto.
     apply Rmult_le_r with(r:=v-u); auto.
     rewrite Rplus_comm in H4; rewrite <- H4.
     unfold Rminus. rewrite Rplus_assoc.
     rewrite Rplus_opp_r; rewrite Rplus_0_r.
     unfold Rdiv. rewrite Rinv_mult_rgt0; auto. }
  apply Theorem4_4. split; auto.
Qed.


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

Fixpoint  power (n:nat) x : R :=
  match n with
  | 0 => 1
  | S p => x * power p x
  end.

Fixpoint accumulation x1 x2 (n i:nat) : R :=
  match i with
  | 0 => power n x1
  | S p => (power (n - S p) x1)*(power (S p) x2) + accumulation x1 x2 n p
  end.

Lemma fix_property : forall x y (n i:nat), (i<=n)%nat ->
  accumulation x y (n+1) i = x*accumulation x y n i.
Proof.
  intros.
  assert(forall x (n:nat), x * power n x = power (n + 1) x).
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


(* 分解定理： x^(n+1) - y^(n+1) = (x-y)*∑(x^(n-i)*y^i) *)
Lemma  decompose_th : forall x y (n:nat),
  power (n+1) x - power (n+1) y = (x-y)*accumulation x y n n.
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
    rewrite (Rmult_plus_distr_l (x-y) (y * power n y) (x * accumulation x y n n)).
    rewrite Rmult_comm with (r2:=(x * accumulation x y n n)).
    rewrite Rmult_assoc with (r1:=x).
    rewrite Rmult_comm with (r1:=accumulation x y n n).
    rewrite <- IHn.
    rewrite Rplus_comm.
    unfold Rminus. rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_l.
    rewrite Rplus_assoc; apply Rplus_eq_compat_l.
    rewrite <- Rplus_assoc.
    assert(forall x (n:nat), x * power n x = power (n + 1) x).
     { intros.
       induction n0; simpl; auto.
       rewrite IHn0; auto. }
    assert(x * - power (n + 1) y + x * (y * power n y) = 0).
     { rewrite <- Rmult_plus_distr_l.
       rewrite H; ring. }
    rewrite H0; rewrite Rplus_0_l.
    rewrite (H y n). ring.
Qed.


Lemma exist_Rgt_lt : forall r1 r2,r1<r2 -> exists r, r1<r<r2.
Proof.
  intros.
  exists ((r1+r2)/2).
  split.
  - apply Rlt_mult. apply Rlt_0_2.
    rewrite Rmult_comm; rewrite double.
    apply Rplus_lt_compat_l with (r:=r1); auto.
  - apply Rgt_lt; apply Rgt_mult. apply Rlt_0_2.
    rewrite Rmult_comm; rewrite double.
    apply Rplus_gt_compat_r with (r:=r2); auto.
Qed.

Lemma strder_Deduce_der : forall F f a b,
  a<b -> str_derivative F f a b -> derivative F f a b.
Proof.
  intros.
  unfold str_derivative in H0.
  unfold derivative.
  exists (fun x => x).
  split.
  - unfold pos_inc.
    split; intros.
    unfold In in H1; unfold oc in H1; tauto.
    apply Rlt_le; auto.
  - split. 
    + unfold bounded_rec_f; intros.
      assert(exists z : R, z ∈ (0, b - a] /\ z < 1/M).
       { assert(0<b-a).
          { apply Rlt_Rminus; auto. }
         generalize (total_order_T (1/M) (b-a)); intro.
         destruct H3. destruct s.
         - generalize(exist_Rgt_lt 0 (1/M)); intro.
           destruct H3.
           unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; auto.
           exists x. unfold In; unfold oc.
           destruct H3. repeat split; auto.
           apply Rlt_le; apply Rlt_trans with (r2:=1/M); auto. 
         - apply Rinv_0_lt_compat in H1.
           apply exist_Rgt_lt in H1. destruct H1, H1.
           exists x. unfold In; unfold oc.
           repeat split; auto. rewrite <- e; apply Rlt_le.
           unfold Rdiv; rewrite Rmult_1_l; auto.
           unfold Rdiv; rewrite Rmult_1_l; auto.
         - generalize H2; auto.
           apply exist_Rgt_lt in H2. destruct H2, H2.
           exists x. unfold In; unfold oc.
           repeat split; auto. apply Rlt_le; auto.
           apply Rlt_trans with (r2:=b-a); auto. }
        destruct H2, H2.
        exists x. split; auto.
        unfold In in H2; unfold oc in H2.
        destruct H2, H4.
        rewrite Rabs_right. unfold Rdiv; rewrite Rmult_1_l.
        unfold Rdiv in H3; rewrite Rmult_1_l in H3.
        apply Rinv_lt_contravar in H3.
        rewrite Rinv_involutive in H3; auto.
        apply Rgt_not_eq; auto.
        apply Rmult_lt_0_compat; auto.
        apply Rinv_0_lt_compat; auto.
        unfold Rdiv; rewrite Rmult_1_l; apply Rgt_ge.
        apply Rlt_gt; apply Rinv_0_lt_compat; auto.
    + destruct H0, H0. exists x. split; auto.
      intros.
      rewrite Rmult_assoc; rewrite <- Rabs_mult.
      rewrite (Rabs_pos_eq (h*h)).
      simpl in H2.
      rewrite <- (Rmult_1_r (h * h)); rewrite Rmult_assoc.
      apply H1; tauto.
      apply Rlt_le; apply Rsqr_pos_lt; tauto.
Qed.


Lemma  accumul_th : forall a b n,
  a>=0 -> b>=0 -> a>b -> accumulation a b n n <= INR(n+1)* power n a /\
  accumulation a b n n >= INR(n+1)%nat* power n b.
Proof.
  intros.
  induction n. simpl.
  rewrite Rmult_1_r.
  split. apply Rle_refl. apply Rge_refl.
  destruct IHn.
  assert(accumulation a b (S n) (S n)=
         a*accumulation a b n n + power(S n) b).
   { simpl.
     rewrite <- Nat.add_1_r.
     rewrite fix_property; try apply Nat.le_refl.
     rewrite Nat.sub_diag. simpl.
     rewrite Rmult_1_l. ring. }
  (* 证明n次幂的性质 *)
  assert(forall n a, power (n+1) a = (power n a) * a).
   { intros. induction n0.
     simpl.
     rewrite Rmult_1_l; rewrite Rmult_1_r; auto.
     simpl. rewrite IHn0; rewrite Rmult_assoc; auto. }
  assert(forall a n, a>=0 -> 0<=power n a).
   { intros.
     induction n0.
     simpl. apply Rlt_le; apply Rlt_0_1.
     simpl. apply Rmult_le_pos; auto. apply Rge_le; auto. }
  split; rewrite H4; rewrite plus_INR.
  - rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    apply Rplus_le_compat.
    rewrite <- Nat.add_1_r.
    rewrite H5.
    rewrite Rmult_comm with (r2:=a).
    rewrite Rmult_comm with (r1:=INR (n + 1)).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l. apply Rge_le; auto.
    rewrite Rmult_comm; auto.
    clear H2 H3 H4 H5.
    induction n.
    simpl. repeat rewrite Rmult_1_r.
    apply Rlt_le; auto.
    simpl in IHn. simpl.
    apply Rle_trans with (r2:=a * (b * power n b)).
    apply Rmult_le_compat_r.
    apply Rmult_le_pos. apply Rge_le; auto.
    apply H6; auto. apply Rlt_le; auto.
    apply Rmult_le_compat_l; auto.
    apply Rge_le; auto.
  - rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    apply Rplus_ge_compat; try apply Rge_refl.
    rewrite <- Nat.add_1_r.
    rewrite H5.
    rewrite Rmult_comm with (r2:=b).
    rewrite Rmult_comm with (r1:=INR (n + 1)).
    rewrite Rmult_assoc. rewrite Rmult_comm with (r1:=power n b).
    apply Rle_ge. apply Rge_le in H3.
    apply Rmult_le_compat; auto. apply Rge_le; auto.
    apply Rmult_le_pos; auto. apply Rlt_le; apply lt_0_INR.
    rewrite Nat.add_1_r; apply gt_Sn_O.
    apply Rlt_le; auto.
Qed.

Lemma factorial_Sn : forall n, factorial (S n) = ((S n)*factorial n)%nat.
Proof.
  intro.
  induction n.
  simpl; auto.
  simpl. ring.
Qed.

Lemma factorial_pos : forall n, 0 < INR(factorial n).
Proof.
  intro.
  induction n.
  simpl. apply Rlt_0_1.
  simpl. rewrite plus_INR.
  apply Rplus_lt_le_0_compat; auto.
  rewrite mult_INR. apply Rmult_le_pos.
  apply pos_INR. apply Rlt_le; auto.
Qed.

Lemma power_inv_fac_der : forall (x m a b:R)(n:nat), x ∈ [a, b] ->
  str_derivative (fun x => m*power(S n)(x-a)/INR(factorial(S n)))
  (fun x => m*power n (x-a)/INR(factorial n)) a b.
Proof.
  intros. apply Theorem4_3. split.
- unfold diff_quo_median. intros.
  assert(u ∈ [u, v] /\ v ∈ [u, v]) as vu_domain.
   { split. unfold In; unfold cc.
     split. apply Rminus_gt; tauto.
     split. apply Rle_refl.
     apply Rlt_le; apply Rminus_gt; tauto.
     unfold In; unfold cc.
     split. apply Rminus_gt; tauto.
     split. apply Rlt_le; apply Rminus_gt; tauto.
     apply Rle_refl. }
     generalize (total_order_T m 0) as order_m; intro.
     assert(v-a>=0 /\ u-a>=0 /\ v-a>u-a) as uv_a_order.
     { destruct H0, H1, H0, H3, H1, H5.
       repeat split.
       apply Rle_ge. apply Rplus_le_reg_r with (r:=a).
       rewrite Rminus_plus_r; rewrite Rplus_0_l; auto.
       apply Rle_ge. apply Rplus_le_reg_r with (r:=a).
       rewrite Rminus_plus_r; rewrite Rplus_0_l; auto.
       apply Rlt_gt. apply Rplus_lt_reg_r with (r:=a).
       repeat rewrite Rminus_plus_r.
       apply Rminus_gt; auto.  }
       destruct order_m. destruct s.
       + exists v, u. split; try tauto. split; try tauto.
         rewrite <- Rdiv_minus_distr.
         rewrite <- Rmult_minus_distr_l.
         rewrite <- Nat.add_1_r.
         rewrite decompose_th.
         assert(v - a - (u - a)=v-u). { ring. }
         rewrite H1. clear H1.
         split; unfold Rdiv; repeat rewrite Rmult_assoc;
         apply Rmult_le_compat_neg_l with (r:=m).
         apply Rlt_le; auto.
         (* 消去v-u *)
         rewrite Rmult_comm;
         repeat rewrite <- Rmult_assoc;
         rewrite Rmult_assoc with (r2:=/(v-u));
         rewrite Rinv_l; try apply Rgt_not_eq; try tauto;
         rewrite Nat.add_1_r; rewrite Rmult_1_r.
         rewrite factorial_Sn. rewrite mult_INR.
         rewrite Rinv_mult_distr.
         rewrite <- Rmult_assoc. apply Rmult_le_compat_r.
         apply Rlt_le; apply Rinv_0_lt_compat; apply factorial_pos.
         apply Rmult_le_reg_r with (r:=INR (S n)).
         rewrite <- Nat.add_1_r; rewrite plus_INR.
         apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1.
         rewrite Rinv_mult_rgt0. rewrite Rmult_comm.
         (* 重要步骤 *)
         destruct uv_a_order, H2.
         apply accumul_th with (n:=n)in H3; auto.
         destruct H3.
         rewrite Nat.add_1_r in H3; auto.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq; apply factorial_pos.
         apply Rlt_le; auto.
         (* 消去v-u *)
         rewrite Rmult_comm with (r1:=v-u).
         repeat rewrite <- Rmult_assoc;
         rewrite Rmult_assoc with (r2:=/(v-u));
         rewrite Rinv_l; try apply Rgt_not_eq; try tauto;
         rewrite Nat.add_1_r; rewrite Rmult_1_r.
         rewrite factorial_Sn with (n:=n). rewrite mult_INR.
         rewrite Rinv_mult_distr.
         rewrite <- Rmult_assoc. apply Rmult_le_compat_r.
         apply Rlt_le; apply Rinv_0_lt_compat; apply factorial_pos.
         apply Rmult_le_reg_r with (r:=INR (S n)).
         rewrite <- Nat.add_1_r; rewrite plus_INR.
         apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1.
         rewrite Rinv_mult_rgt0. rewrite Rmult_comm.
         (* 重要步骤 *)
         destruct uv_a_order, H2.
         apply accumul_th with (n:=n)in H3; auto.
         destruct H3.
         rewrite Nat.add_1_r in H4; auto.
         apply Rge_le; auto.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq; apply factorial_pos.
       + exists u, v. split; try tauto.
         split; try tauto.
         repeat rewrite e.
         unfold Rdiv.
         repeat rewrite Rmult_0_l.
         rewrite Rminus_diag_eq; auto.
         rewrite Rmult_0_l.
         split; apply Rle_refl.
       + exists u, v. split; try tauto. split; try tauto.
         rewrite <- Rdiv_minus_distr.
         rewrite <- Rmult_minus_distr_l.
         rewrite <- Nat.add_1_r with (n:=n).
         rewrite decompose_th.
         assert(v - a - (u - a)=v-u). { ring. }
         rewrite H1. clear H1.
         split; unfold Rdiv; repeat rewrite Rmult_assoc.
         apply Rmult_le_compat_l with (r:=m).
         apply Rlt_le; auto.
         (* 消去v-u *)
         rewrite Rmult_comm with (r1:=v-u);
         repeat rewrite <- Rmult_assoc;
         rewrite Rmult_assoc with (r2:=/(v-u));
         rewrite Rinv_l; try apply Rgt_not_eq; try tauto;
         rewrite Nat.add_1_r; rewrite Rmult_1_r.
         rewrite factorial_Sn with (n:=n). rewrite mult_INR.
         rewrite Rinv_mult_distr.
         rewrite <- Rmult_assoc. apply Rmult_le_compat_r.
         apply Rlt_le; apply Rinv_0_lt_compat; apply factorial_pos.
         apply Rmult_le_reg_r with (r:=INR (S n)).
         rewrite <- Nat.add_1_r; rewrite plus_INR.
         apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1.
         rewrite Rinv_mult_rgt0. rewrite Rmult_comm.
         (* 重要步骤 *)
         destruct uv_a_order, H2.
         apply accumul_th with (n:=n)in H3; auto.
         destruct H3.
         rewrite Nat.add_1_r in H4; auto.
         apply Rge_le; auto.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq; apply factorial_pos.
         apply Rmult_le_compat_l with (r:=m).
         apply Rlt_le; auto.
         (* 消去v-u *)
         rewrite Rmult_comm;
         repeat rewrite <- Rmult_assoc;
         rewrite Rmult_assoc with (r2:=/(v-u));
         rewrite Rinv_l; try apply Rgt_not_eq; try tauto;
         rewrite Nat.add_1_r; rewrite Rmult_1_r.
         rewrite factorial_Sn. rewrite mult_INR.
         rewrite Rinv_mult_distr.
         rewrite <- Rmult_assoc. apply Rmult_le_compat_r.
         apply Rlt_le; apply Rinv_0_lt_compat; apply factorial_pos.
         apply Rmult_le_reg_r with (r:=INR (S n)).
         rewrite <- Nat.add_1_r; rewrite plus_INR.
         apply Rplus_le_lt_0_compat. apply pos_INR. apply Rlt_0_1.
         rewrite Rinv_mult_rgt0. rewrite Rmult_comm.
         (* 重要步骤 *)
         destruct uv_a_order, H2.
         apply accumul_th with (n:=n)in H3; auto.
         destruct H3.
         rewrite Nat.add_1_r in H3; auto.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq; apply factorial_pos.
     - generalize(Real_Order m 0); intro.
       destruct H0.
       + exists 1.
         split. apply Rlt_0_1.
         intros.
         repeat rewrite H0.
         unfold Rdiv; repeat rewrite Rmult_0_l.
         rewrite Rminus_diag_eq; auto.
         rewrite Rmult_1_l. rewrite Rabs_R0. apply Rabs_pos.
       + generalize(Nat.eq_0_gt_0_cases n); intro.
         destruct H1.
         { exists 1. split. apply Rlt_0_1. rewrite H1.
           intros. simpl. unfold Rdiv. rewrite Rinv_r_simpl_l.
           rewrite Rminus_diag_eq; auto. rewrite Rmult_1_l.
           SearchAbout(Rabs 0). rewrite Rabs_R0; apply Rabs_pos.
           apply Rgt_not_eq; apply Rlt_0_1. }
         { exists (Rabs(m*(power (n-1) (b-a))/INR(factorial (n-1)))).
           split. admit.
           intros.
           unfold Rdiv; repeat rewrite Rmult_assoc.
           rewrite <- Rmult_minus_distr_l.
           rewrite Rabs_mult. rewrite Rabs_mult.
           rewrite Rmult_assoc; apply Rmult_le_compat_l. apply Rabs_pos.
           rewrite Rmult_comm. 
           assert(n=S(n-1)).
            { rewrite <- Nat.add_1_r.
              rewrite Nat.sub_add; auto. }
           rewrite H3. rewrite <- Nat.add_1_r.
           rewrite Rmult_comm with (r1:=power (n - 1 + 1) (x0 - a)).
           rewrite <- Rmult_minus_distr_l.
           rewrite decompose_th.
           assert(x0 + h - a - (x0 - a)=h). { ring. }
           rewrite H4. clear H4.
           rewrite Rmult_comm; rewrite Rmult_assoc.
           rewrite Rabs_mult with (x:=h). rewrite Rmult_comm with (r2:=Rabs h).
           apply Rmult_le_compat_l. apply Rabs_pos. admit.
Admitted.


(* Taylor公式的预备定理 *)

(* 若H在[a,b]上n阶一致(强)可导（n为正整数），且有
    (1) 在[a,b]上有..... *)


Parameter N_der : (R->R)->nat->R->R.

Axiom N_uniform_str_derivative : forall F a b (n:nat),
  str_derivative (N_der F n) (N_der F (S n)) a b.

(*N阶强可导*)
Fixpoint N_uniform_str_derivability F a b (n:nat) : Prop :=
  match n with
  | 0 => False
  | 1 => str_derivative F (N_der F 1) a b
  | S (S p) =>  str_derivative F (N_der F (S p)) a b /\
                   N_uniform_str_derivability (N_der F (S p)) a b p
  end.

Theorem Taylor_Lemma : forall H a b (n:nat), (n>0)%nat ->
  N_uniform_str_derivability H a b n ->
  (forall k, (k<n)%nat -> N_der H k a = 0 /\ N_der H 0  = H ) ->
  forall m M, (forall x, x ∈ [a,b] -> m <= N_der H n x <= M) ->
  forall k, (k<=n)%nat -> forall x, x ∈ [a,b] -> 
  m*power k (x-a)/INR (factorial k) <= N_der H (n-k) x <=
  M*power k (x-a)/ INR(factorial k).
Proof.
  intros H a b n H0 H1 H2 m M H3 k H4.
  induction k.
  - simpl. intros. unfold Rdiv.
    repeat rewrite Rinv_r_simpl_l; try apply R1_neq_R0.
    apply H3 in H5; try apply Nat.le_refl.
    rewrite Nat.sub_0_r; auto.
  - assert((k<=n)%nat) as le_k_n.
     { apply Nat.le_trans with (m:= S k); auto. }
    generalize(IHk le_k_n) as IHk_x; intros. clear IHk.
    generalize(power_inv_fac_der x m a b k H5); intro.
    generalize(power_inv_fac_der x M a b k H5); intro.
    assert(str_derivative (N_der H (n-S k))(N_der H(n-k)) a b).
     { assert((n-S k=n-k-1 /\ n-k=S(n-k-1))%nat).
        { split. auto.
          rewrite <- Nat.sub_add_distr. rewrite Nat.add_1_r; auto.
          rewrite <- Nat.add_1_r.
          rewrite Nat.sub_add; auto.
          apply plus_le_reg_l with (p:=k).
          rewrite Nat.add_comm with (m:=(n-k)%nat).
          rewrite Nat.sub_add. rewrite Nat.add_1_r; auto.
          apply Nat.le_trans with (m:=S k); auto. }
       destruct H8. rewrite H8. rewrite H9 at 2.
       apply N_uniform_str_derivative. } 
    assert(a<=x) as le_a_x.
     { unfold In in H5. unfold cc in H5. tauto. }
    split.
    + destruct le_a_x.
      * apply Theorem3_1_1' with (c:=-1) in H6.
        apply (Theorem3_1_2' _ _ _ _ _ _ H8) in H6.
        apply Theorem4_3 in H6. destruct H6. clear H10.
        unfold diff_quo_median in H6.
        assert(a ∈ [a, b] /\ x ∈ [a, b] /\ x - a > 0).
          { destruct H5, H10. repeat split; auto.
            apply Rle_refl. apply Rlt_le; auto.
            apply Rgt_minus; auto. }
        apply H6 in H10.
        destruct H10, H10, H10, H11, H12. clear H6 H13.
        unfold plus_Fu in H12; unfold mult_real_f in H12.
        assert(n-S k<n)%nat.
         { apply Nat.sub_lt; auto. apply Nat.lt_0_succ. }
        apply H2 in H6. destruct H6. rewrite H6 in H12.
        rewrite Rminus_diag_eq with(r1:=a) in H12; auto.
        rewrite Rplus_0_l in H12.
        assert(power (S k) 0 = 0).
         { simpl. rewrite Rmult_0_l; auto. }
        rewrite H14 in H12. rewrite Rmult_0_r in H12.
        unfold Rdiv in H12; rewrite Rmult_0_l in H12.
        rewrite Rmult_0_r in H12.
        assert(x0 ∈ [a, b]).
         { destruct H5, H15, H10, H17.
           split; auto. split; auto.
           apply Rle_trans with (r2:=x); auto. }
        apply IHk_x in H15.
        apply Rplus_le_reg_r with 
          (r:=-(m*power(S k)(x-a)/INR(factorial(S k)))).
        rewrite Rplus_opp_r. destruct H15. clear H16.
        apply Rplus_le_compat_r with 
          (r:=-(m*power k (x0-a)/INR(factorial k))) in H15.
        rewrite Rplus_opp_r in H15. unfold Rdiv in H15.
        repeat rewrite Ropp_mult_distr_l_reverse with (r1:=1)in H12.
        repeat rewrite Rmult_1_l in H12.
        apply Rle_trans with (r1:=0)in H12; auto.
        unfold Rdiv. rewrite Rminus_0_r in H12.
        apply Rmult_le_reg_r with (r:= / (x - a)).
        apply Rinv_0_lt_compat; apply Rlt_Rminus; auto.
        rewrite Rmult_0_l; auto.
      * rewrite <- H9. rewrite Rminus_diag_eq; auto.
        simpl. rewrite Rmult_0_l. rewrite Rmult_0_r.
        unfold Rdiv; rewrite Rmult_0_l.
        assert(n - S k < n)%nat.
         { apply Nat.sub_lt; auto. apply Nat.lt_0_succ. }
        apply H2 in H10. destruct H10;
        rewrite H10; apply Rle_refl.
    + destruct le_a_x.
      * apply Theorem3_1_1' with (c:=-1) in H7.
        apply (Theorem3_1_2' _ _ _ _ _ _ H8) in H7.
        apply Theorem4_3 in H7. destruct H7. clear H10.
        unfold diff_quo_median in H7.
        assert(a ∈ [a, b] /\ x ∈ [a, b] /\ x - a > 0).
         { destruct H5, H10. repeat split; auto.
           apply Rle_refl. apply Rlt_le; auto.
           apply Rgt_minus; auto. }
        apply H7 in H10.
        destruct H10, H10, H10, H11, H12. clear H7 H12.
        unfold plus_Fu in H13; unfold mult_real_f in H13.
        assert(n - S k < n)%nat.
         { apply Nat.sub_lt; auto. apply Nat.lt_0_succ. }
        apply H2 in H7. destruct H7. rewrite H7 in H13.
        rewrite Rminus_diag_eq with(r1:=a) in H13; auto.
        rewrite Rplus_0_l in H13.
        assert(power (S k) 0 = 0).
         { simpl. rewrite Rmult_0_l; auto. }
        rewrite H14 in H13. rewrite Rmult_0_r in H13.
        unfold Rdiv in H13; rewrite Rmult_0_l in H13.
        rewrite Rmult_0_r in H13.
        assert(x1 ∈ [a, b]).
         { destruct H5, H15, H11, H17.
           split; auto. split; auto.
           apply Rle_trans with (r2:=x); auto. }
        apply IHk_x in H15.
        apply Rplus_le_reg_r with 
          (r:=-(M*power(S k)(x-a)/INR(factorial(S k)))).
        rewrite Rplus_opp_r. destruct H15. clear H15.
        apply Rplus_le_compat_r with 
          (r:=-(M*power k (x1-a)/INR(factorial k))) in H16.
        rewrite Rplus_opp_r in H16. unfold Rdiv in H16.
        repeat rewrite Ropp_mult_distr_l_reverse with (r1:=1)in H13.
        repeat rewrite Rmult_1_l in H13.
        apply Rle_trans with (r3:=0)in H13; auto.
        unfold Rdiv. rewrite Rminus_0_r in H13.
        apply Rmult_le_reg_r with (r:=/(x-a)).
        apply Rinv_0_lt_compat; apply Rlt_Rminus; auto.
        rewrite Rmult_0_l; auto.
      * rewrite <- H9. rewrite Rminus_diag_eq; auto.
        simpl. rewrite Rmult_0_l. rewrite Rmult_0_r.
        unfold Rdiv; rewrite Rmult_0_l.
        assert(n-S k<n)%nat.
         { apply Nat.sub_lt; auto. apply Nat.lt_0_succ. }
        apply H2 in H10. destruct H10; rewrite H10; apply Rle_refl.
Qed.

Fixpoint Taylor_Formula F (x:R) c n :=
  match n with
  | 0 => 0
  | 1 => F c
  | S p => (N_der F p c)*(power p (x-c))/INR(factorial p)+
           Taylor_Formula F x c p
  end. 

Lemma Taylor_Nder: forall F n M a b c,
  N_uniform_str_derivability F a b n -> c ∈ [a, b] ->
  (forall x, x ∈ [a, b] -> Rabs(N_der F n x)<=M) ->
  (N_uniform_str_derivability (fun x:R => F x-Taylor_Formula F x c n) c b n /\
  (forall k, (k<n)%nat -> N_der (fun x => F x-Taylor_Formula F x c n) k c = 0)
   /\ N_der (fun x => F x-Taylor_Formula F x c n) 0=
  (fun x => F x-Taylor_Formula F x c n)/\
  (forall x, x ∈ [a,b] -> -M <= N_der (fun x => F x-Taylor_Formula F x c n) n x <= M)).
Admitted.

Lemma Rabs_le_reg : forall a b : R,  Rabs a <= b -> - b <= a <= b.
Proof.
  intros.
  assert(0<=b).
   { apply Rle_trans with (r1:=0) in H; auto.
     apply Rabs_pos. }
  rewrite <- Rabs_pos_eq in H; auto.
  apply Rsqr_le_abs_1 in H.
  generalize(H) as H1; intro.
  apply Rsqr_neg_pos_le_0 in H; auto.
  apply Rsqr_incr_0_var in H1; auto.
Qed.


Lemma Domain_x_c : forall a b x c,
  c ∈ [a, b] -> x ∈ [a, b]-> x ∈ [c, b]\/x ∈ [a, c].
Proof.
  intros.
  generalize(Real_Order a c); intro.
  generalize(Real_Order b c); intro.
  destruct H1.
  - rewrite <- H1. left; auto.
  - destruct H2.
    + rewrite <- H2. right; auto.
    + generalize(Rle_or_lt x c); intro.
      destruct H, H0, H4, H5. destruct H3.
      * right. unfold In; unfold cc.
        destruct H4; auto.
        contradiction.
      * left. unfold In; unfold cc.
        apply Rlt_le in H3.
        destruct H6; auto.
        apply eq_sym in H6.
        contradiction.
Qed.

Lemma Taylor_Nder' : forall F n M a b c,
  N_uniform_str_derivability F a b n -> c ∈ [a, b] ->
  (forall x, x ∈ [a, b] -> Rabs(N_der F n x)<=M) ->
  (N_uniform_str_derivability(fun x:R => F (-x)-Taylor_Formula F (-x) c n)(-c)(-a) n) /\
  (forall k, (k<n)%nat -> N_der (fun x => F (-x)-Taylor_Formula F (-x) c n) k (-c) = 0) /\
  N_der (fun x => F (-x)-Taylor_Formula F (-x) c n) 0 = (fun x => F (-x)-Taylor_Formula F (-x) c n) /\
  (forall x, x ∈ [-c,-a] -> -M <= N_der (fun x => F (-x)-Taylor_Formula F (-x) c n) n x <= M).
Admitted.

Lemma power_x_pos : forall x n, 0<=x -> 0 <= power n x.
Proof.
  intros.
  induction n.
  - simpl. apply Rle_0_1.
  - simpl. apply Rmult_le_pos; auto.
Qed.

Lemma Rabs_power : forall a b n,
 Rabs (power n (-a-b))=Rabs(power n (a+b)).
Proof.
  intros.
  induction n.
  - simpl; auto.
  - simpl. repeat rewrite Rabs_mult.
    rewrite IHn. apply Rmult_eq_compat_r.
    unfold Rminus. rewrite <- Ropp_plus_distr.
    rewrite Rabs_Ropp; auto.
Qed.

Theorem Taylor_Theorem : forall F a b n M, (n>0)%nat ->
  N_uniform_str_derivability F a b n ->
  (forall F, N_der F 0= F) -> 
  (forall x, x ∈ [a, b] -> Rabs(N_der F n x)<=M) ->
  forall c x, c ∈ [a, b] -> x ∈ [a, b] -> 
  Rabs(F(x)-(Taylor_Formula F x c n))<=
  M*Rabs(power n (x-c))/INR(factorial n).
Proof.
  intros.
  generalize H3 as Domain_c; intro.
  apply Domain_x_c with (x:=x) in H3; auto.
  destruct H3.
  - apply Rabs_le.
    rewrite Rabs_pos_eq; try apply power_x_pos.
    assert(-(M*power n (x-c)/INR(factorial n))=
            -M*power n (x-c)/INR(factorial n)).
     { unfold Rdiv. repeat rewrite Rmult_assoc.
       rewrite Ropp_mult_distr_l; auto. }
    rewrite H5. clear H5.
    assert(N_der (fun x => F x-Taylor_Formula F x c n) 0 x =
           F x-Taylor_Formula F x c n). { rewrite H1; auto. }
    rewrite <- H5. clear H5.
    rewrite <- Nat.sub_diag with (n:=n).
    apply Taylor_Nder with(c:=c)(M:=M) in H0; auto.
    destruct H0.
    apply Taylor_Lemma with (b:=b); try tauto.
    intros. apply H5 in H6. split; auto.
    destruct H5; auto. destruct H6.
    intros. apply H7; auto.
    split. destruct H4; auto.
    destruct Domain_c, H10, H8, H12.
    split; auto. apply Rle_trans with (r2:=c); auto.
    apply Nat.le_refl. destruct H3, H5.
    apply Rge_le. apply Rge_minus; apply Rle_ge; auto.
  - assert(exists u, x = -u). { exists (0-x). ring. }
    destruct H5. rename x0 into u.
    rewrite H5.
    assert(u ∈ [-c, -a]).
     { destruct H3. split. apply Ropp_lt_contravar; auto.
       assert(u = - x). { rewrite H5. ring. }
       destruct H6. rewrite H7.
       split; apply Ropp_le_contravar; auto. }
    rewrite Rabs_power. apply Rabs_le.
    rewrite Rabs_pos_eq; try apply power_x_pos.
    assert(-(M*power n (u+c)/INR(factorial n))=
            -M*power n (u+c)/INR(factorial n)).
     { unfold Rdiv. repeat rewrite Rmult_assoc.
       rewrite Ropp_mult_distr_l; auto. }
    rewrite H7. clear H7.
    assert(u+c=u-(-c)). { ring. } rewrite H7.
    assert(N_der (fun x => F (-x)-Taylor_Formula F (-x) c n) 0 u =
           F (-u)-Taylor_Formula F (-u) c n). { rewrite H1; auto. }
    rewrite <- H8. clear H8.
    apply Taylor_Nder' with (c:=c)(M:=M) in H0; auto.
    destruct H0. rewrite <- Nat.sub_diag with (n:=n).
    apply Taylor_Lemma with (b:=(-a)); auto.
    intros. destruct H8. apply H8 in H9; auto.
    intros. destruct H8, H10 ; auto.
    assert(u+c=u-(-c)). { ring. }
    apply Rge_le. rewrite H7. destruct H6, H8. 
    apply Rge_minus; apply Rle_ge; auto.
Qed.
