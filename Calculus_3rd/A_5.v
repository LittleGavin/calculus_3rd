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

(*阶乘*)
Fixpoint  factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S p => S p * (factorial p)
  end.

(*实数x的n次幂*)
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


(* x^(n+1) - y^(n+1) = (x-y)*∑(x^(n-i)*y^i) *)
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


Lemma  accumul_th' : forall a b n,
  a>=0 -> b>=0 -> a<b -> accumulation a b n n <= INR(n+1)* power n b /\
  accumulation a b n n >= INR(n+1)%nat* power n a.
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
    rewrite Rmult_comm with (r2:=b).
    rewrite Rmult_comm with (r1:=INR (n + 1)).
    rewrite Rmult_assoc. apply Rmult_le_compat.
    apply Rge_le; auto. clear H2 H3 H4.
    assert(forall k, 0 <= accumulation a b n k).
     { intro. induction k.
       simpl. apply H6; auto.
       simpl. apply Rplus_le_le_0_compat; auto.
       apply Rmult_le_pos. apply H6; auto.
       apply Rmult_le_pos; auto. apply Rge_le; auto. }
    apply H2. apply Rlt_le; auto.
    rewrite Rmult_comm; auto. apply Rle_refl.
  - rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    apply Rplus_ge_compat; try apply Rge_refl.
    rewrite <- Nat.add_1_r.
    rewrite H5.
    rewrite Rmult_comm with (r2:=a).
    rewrite Rmult_comm with (r1:=INR (n + 1)).
    rewrite Rmult_assoc. rewrite Rmult_comm with (r1:=power n a).
    apply Rle_ge. apply Rge_le in H3.
    apply Rmult_le_compat; auto. apply Rge_le; auto.
    apply Rmult_le_pos; auto. apply Rlt_le; apply lt_0_INR.
    rewrite Nat.add_1_r; apply gt_Sn_O. apply Rle_refl.
    assert(forall a b n, a>=0 -> b>=0 -> a<=b -> power n a <= power n b).
    { intros. induction n0.
      simpl; apply Rle_refl.
      simpl. apply Rmult_le_compat; auto.
      apply Rge_le; auto. } apply Rle_ge; apply H7; auto.
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


Lemma accumul_abc_bigger : forall a b c n, a>=0 -> b>=0 -> c>=0 -> a<=b ->
  b<=c -> accumulation b a n n <= INR(n+1)%nat* power n c.
Proof.
  intros.
  assert(forall a b n, a>=0 -> b>=0 -> a<=b -> power n a <= power n b).
   { intros. induction n0.
     simpl; apply Rle_refl.
     simpl. apply Rmult_le_compat; auto.
     apply Rge_le; auto. clear IHn0.
     induction n0. simpl. apply Rle_0_1.
     simpl. apply Rmult_le_pos; auto.
     apply Rge_le; auto. }
  destruct H2.
  generalize( accumul_th b a n H0 H H2); intro.
  destruct H5. apply Rle_trans with (r2:=INR (n + 1) * power n b); auto.
  apply Rmult_le_compat_l. apply pos_INR.
  apply H4; auto.
  rewrite H2.
  assert(forall a n, accumulation a a n n = INR (n + 1) * power n a).
   { intros. induction n0.
     simpl. ring.
     assert(accumulation a0 a0 (S n0) (S n0)=
         a0*accumulation a0 a0 n0 n0 + power(S n0) a0).
      { simpl.
        rewrite <- Nat.add_1_r.
        rewrite fix_property; try apply Nat.le_refl.
        rewrite Nat.sub_diag. simpl.
        rewrite Rmult_1_l. ring. }
     rewrite H5. rewrite IHn0. rewrite Rmult_comm.
     rewrite Rmult_assoc.
     assert(power n0 a0 * a0 = power (S n0) a0).
      { simpl. ring. } rewrite H6.
     rewrite <- Rmult_1_l with (r:=power (S n0) a0) at 2.
     rewrite <- Rmult_plus_distr_r. apply Rmult_eq_compat_r.
     rewrite Nat.add_comm with (n:= S n0).
     rewrite  S_O_plus_INR. rewrite Nat.add_1_r.
     rewrite Rplus_comm. apply Rplus_eq_compat_r; auto. }
  rewrite H5. apply Rmult_le_compat_l. apply pos_INR.
  apply H4; auto.
Qed.


Lemma accumul_abc_bigger' : forall a b c n, a>=0 -> b>=0 -> c>=0 -> a>=b ->
  a<=c -> accumulation b a n n <= INR(n+1)%nat* power n c.
Proof.
  intros.
  assert(forall a b n, a>=0 -> b>=0 -> a<=b -> power n a <= power n b).
   { intros. induction n0.
     simpl; apply Rle_refl.
     simpl. apply Rmult_le_compat; auto.
     apply Rge_le; auto. clear IHn0.
     induction n0. simpl. apply Rle_0_1.
     simpl. apply Rmult_le_pos; auto.
     apply Rge_le; auto. }
  destruct H2.
  generalize( accumul_th' b a n H0 H H2); intro.
  destruct H5. apply Rle_trans with (r2:=INR (n + 1) * power n a); auto.
  apply Rmult_le_compat_l. apply pos_INR.
  apply H4; auto.
  rewrite H2.
  assert(forall a n, accumulation a a n n = INR (n + 1) * power n a).
   { intros. induction n0.
     simpl. ring.
     assert(accumulation a0 a0 (S n0) (S n0)=
         a0*accumulation a0 a0 n0 n0 + power(S n0) a0).
      { simpl.
        rewrite <- Nat.add_1_r.
        rewrite fix_property; try apply Nat.le_refl.
        rewrite Nat.sub_diag. simpl.
        rewrite Rmult_1_l. ring. }
     rewrite H5. rewrite IHn0. rewrite Rmult_comm.
     rewrite Rmult_assoc.
     assert(power n0 a0 * a0 = power (S n0) a0).
      { simpl. ring. } rewrite H6.
     rewrite <- Rmult_1_l with (r:=power (S n0) a0) at 2.
     rewrite <- Rmult_plus_distr_r. apply Rmult_eq_compat_r.
     rewrite Nat.add_comm with (n:= S n0).
     rewrite  S_O_plus_INR. rewrite Nat.add_1_r.
     rewrite Rplus_comm. apply Rplus_eq_compat_r; auto. }
  rewrite H5. apply Rmult_le_compat_l. apply pos_INR.
  apply H4; auto. rewrite H2 in H3; auto.
Qed.


Lemma power_inv_fac_der : forall (m a b:R)(n:nat), a < b ->
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
         apply Rlt_le; auto. rewrite Rmult_comm;
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
         destruct uv_a_order, H2.
         apply accumul_th with (n:=n)in H3; auto.
         destruct H3.
         rewrite Nat.add_1_r in H3; auto.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq; apply factorial_pos.
         apply Rlt_le; auto.
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
         destruct uv_a_order, H2.
         apply accumul_th with (n:=n)in H3; auto.
         destruct H3.
         rewrite Nat.add_1_r in H3; auto.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq.
         apply lt_0_INR; apply Nat.lt_0_succ.
         apply Rgt_not_eq; apply factorial_pos.
     - generalize(total_eq_or_neq m 0); intro.
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
           rewrite Rabs_R0; apply Rabs_pos.
           apply Rgt_not_eq; apply Rlt_0_1. }
         { exists (Rabs(m*(power (n-1) (b-a))/INR(factorial (n-1)))).
           split. intros.
           assert(forall (a b: R)(n:nat), a<b -> (0 < n)%nat ->
             Rabs (m * power (n - 1) (b - a) / INR (factorial (n - 1))) > 0 ).
           { intros. apply Rabs_pos_lt.
             apply Rmult_integral_contrapositive_currified.
             apply Rmult_integral_contrapositive_currified; auto.
             induction (n0-1)%nat. simpl. apply Rgt_not_eq. apply Rlt_0_1.
             simpl. apply Rmult_integral_contrapositive_currified; auto.
             apply Rgt_not_eq; auto. apply Rgt_minus; auto.
             apply Rinv_neq_0_compat. apply Rgt_not_eq. apply factorial_pos. }
           apply H2; auto.
           intros. unfold Rdiv; repeat rewrite Rmult_assoc.
           rewrite <- Rmult_minus_distr_l.
           rewrite Rabs_mult. rewrite Rabs_mult.
           rewrite Rmult_assoc; apply Rmult_le_compat_l. apply Rabs_pos.
           rewrite Rmult_comm. 
           assert(n=S(n-1)).
            { rewrite <- Nat.add_1_r.
              rewrite Nat.sub_add; auto. }
           rewrite H3. rewrite <- Nat.add_1_r.
           rewrite Rmult_comm with (r1:=power (n - 1 + 1) (x - a)).
           rewrite <- Rmult_minus_distr_l.
           rewrite decompose_th.
           assert(x + h - a - (x - a)=h). { ring. }
           rewrite H4. clear H4.
           rewrite Rmult_comm; rewrite Rmult_assoc.
           rewrite Rabs_mult with (x:=h). 
           rewrite Rmult_comm with (r2:=Rabs h).
           apply Rmult_le_compat_l. apply Rabs_pos.
           assert(n-1+1-1 = n-1)%nat. { rewrite Nat.add_sub; auto. }
           rewrite H4. rewrite Nat.sub_add; try apply lt_le_S; auto.
           clear H3 H4.
           destruct H2, H2, H4, H3, H6.
           generalize(total_le_gt (x+h) x); intro.
           assert(x + h - a >= 0 /\ x - a >= 0) as gt_0_x0h.
            { split. apply Rge_minus. apply Rle_ge; auto.
              apply Rge_minus; apply Rle_ge; auto. }
           destruct H8.
           assert(x-a>=x+h-a). { unfold Rminus. apply Rle_ge. apply Rplus_le_compat_r; auto. }
           apply accumul_abc_bigger' with (c:=b - a)(n:=(n-1)%nat) in H8; try tauto.
           repeat rewrite Rabs_right.
           apply Rmult_le_reg_r with (r:=INR (factorial (n - 1))).
           apply factorial_pos. rewrite Rinv_mult_rgt0; try apply factorial_pos.
           assert(forall k, INR (factorial (S k)) = INR(S k) * INR(factorial k)). 
            { intros. induction k. simpl. ring.
              rewrite IHk.
              simpl. destruct k. simpl. ring.
              assert(factorial(S k)+S k*factorial(S k) = (S k+1)*factorial(S k))%nat.
               { ring. } rewrite H9.
              assert((S k+1)*factorial(S k)+((S k+1)*factorial(S k)+S k*((S k+1)*factorial(S k))) = 
                (S k+1+1)*(S k+1)*factorial(S k))%nat.
                { ring. } rewrite H10. repeat rewrite mult_INR.
              assert((INR(S k)+1+1) = INR(S k+1+1)). { repeat rewrite plus_INR; auto. }
              assert((INR(S k)+1) = INR(S k+1)). { rewrite plus_INR; auto. }
              rewrite H11. rewrite H12; auto. rewrite <- Rmult_assoc; auto. }
              assert(accumulation (x + h - a) (x - a) (n - 1) (n - 1) * / INR (factorial n) *
 INR (factorial (n - 1)) = accumulation (x + h - a) (x - a) (n - 1) (n - 1) * /INR n).
               { assert(S(n-1) = n).
                   { rewrite <- Nat.sub_add with (n:=1%nat).
                     rewrite Nat.add_1_r; auto. apply lt_le_S; auto. }
                 rewrite <- H10 at 3. rewrite H9. rewrite Rinv_mult_distr.
                 rewrite <- Rmult_assoc. rewrite Rinv_mult_rgt0. rewrite H10; auto.
                 apply factorial_pos. rewrite H10. apply Rgt_not_eq; apply lt_0_INR; auto.
                 apply Rgt_not_eq; apply factorial_pos. }
               rewrite H10. rewrite Nat.sub_add in H8.
               apply Rmult_le_reg_r with (r:=INR n). apply lt_0_INR; auto.
               rewrite Rinv_mult_rgt0. rewrite Rmult_comm; auto. apply lt_0_INR; auto.
               apply lt_le_S; auto.
               apply Rle_ge; apply Rmult_le_pos.
               clear H8. induction(n-1)%nat. simpl. apply Rle_0_1.
               simpl. apply Rmult_le_pos; auto.
               apply Rlt_le; apply Rlt_Rminus; auto.
               apply Rlt_le; apply Rinv_0_lt_compat; apply factorial_pos.
               apply Rle_ge; apply Rmult_le_pos.
               assert(forall a n, a>=0 -> 0<=power n a).
                { intros. induction n0.
                  simpl. apply Rlt_le; apply Rlt_0_1.
                  simpl. apply Rmult_le_pos; auto. apply Rge_le; auto. }
               assert(forall a b n k, a>=0 -> b>=0 -> 0 <= accumulation a b n k).
                { intros. induction k.
                  simpl. apply H9; auto.
                  simpl. apply Rplus_le_le_0_compat; auto.
                  apply Rmult_le_pos. apply H9; auto.
                  apply Rmult_le_pos; auto. apply Rge_le; auto. }
               apply H10; try tauto. apply Rlt_le; apply Rinv_0_lt_compat.
               apply factorial_pos. apply Rge_minus.
               apply Rgt_ge; apply Rlt_gt; auto.
               unfold Rminus. apply Rplus_le_compat_r; auto.
               assert(x-a<=x+h-a). { unfold Rminus. apply Rlt_le; apply Rplus_lt_compat_r; auto. }
               apply accumul_abc_bigger with (c:=b - a)(n:=(n-1)%nat) in H8; try tauto.
               repeat rewrite Rabs_right.
           apply Rmult_le_reg_r with (r:=INR (factorial (n - 1))).
           apply factorial_pos. rewrite Rinv_mult_rgt0; try apply factorial_pos.
           assert(forall k, INR (factorial (S k)) = INR(S k) * INR(factorial k)). 
            { intros. induction k. simpl. ring.
              rewrite IHk.
              simpl. destruct k. simpl. ring.
              assert(factorial(S k)+S k*factorial(S k) = (S k+1)*factorial(S k))%nat.
               { ring. } rewrite H9.
              assert((S k+1)*factorial(S k)+((S k+1)*factorial(S k)+S k*((S k+1)*factorial(S k))) = 
                (S k+1+1)*(S k+1)*factorial(S k))%nat.
                { ring. } rewrite H10. repeat rewrite mult_INR.
              assert((INR(S k)+1+1) = INR(S k+1+1)). { repeat rewrite plus_INR; auto. }
              assert((INR(S k)+1) = INR(S k+1)). { rewrite plus_INR; auto. }
              rewrite H11. rewrite H12; auto. rewrite <- Rmult_assoc; auto. }
              assert(accumulation (x + h - a) (x - a) (n - 1) (n - 1) * / INR (factorial n) *
 INR (factorial (n - 1)) = accumulation (x + h - a) (x - a) (n - 1) (n - 1) * /INR n).
               { assert(S(n-1) = n).
                   { rewrite <- Nat.sub_add with (n:=1%nat).
                     rewrite Nat.add_1_r; auto. apply lt_le_S; auto. }
                 rewrite <- H10 at 3. rewrite H9. rewrite Rinv_mult_distr.
                 rewrite <- Rmult_assoc. rewrite Rinv_mult_rgt0. rewrite H10; auto.
                 apply factorial_pos. rewrite H10. apply Rgt_not_eq; apply lt_0_INR; auto.
                 apply Rgt_not_eq; apply factorial_pos. }
               rewrite H10. rewrite Nat.sub_add in H8.
               apply Rmult_le_reg_r with (r:=INR n). apply lt_0_INR; auto.
               rewrite Rinv_mult_rgt0. rewrite Rmult_comm; auto. apply lt_0_INR; auto.
               apply lt_le_S; auto.
               apply Rle_ge; apply Rmult_le_pos.
               clear H8. induction(n-1)%nat. simpl. apply Rle_0_1.
               simpl. apply Rmult_le_pos; auto.
               apply Rlt_le; apply Rlt_Rminus; auto.
               apply Rlt_le; apply Rinv_0_lt_compat; apply factorial_pos.
               apply Rle_ge; apply Rmult_le_pos.
               assert(forall a n, a>=0 -> 0<=power n a).
                { intros. induction n0.
                  simpl. apply Rlt_le; apply Rlt_0_1.
                  simpl. apply Rmult_le_pos; auto. apply Rge_le; auto. }
               assert(forall a b n k, a>=0 -> b>=0 -> 0 <= accumulation a b n k).
                { intros. induction k.
                  simpl. apply H9; auto.
                  simpl. apply Rplus_le_le_0_compat; auto.
                  apply Rmult_le_pos. apply H9; auto.
                  apply Rmult_le_pos; auto. apply Rge_le; auto. }
               apply H10; try tauto. apply Rlt_le; apply Rinv_0_lt_compat.
               apply factorial_pos. apply Rge_minus.
               apply Rgt_ge; apply Rlt_gt; auto.
               unfold Rminus. apply Rplus_le_compat_r; auto. }
Qed.

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
  generalize(total_eq_or_neq a c); intro.
  generalize(total_eq_or_neq b c); intro.
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

Lemma Rabs_power_opp : forall n, Rabs (power n (-1)) = 1.
Proof.
  intro.
  induction n. simpl. apply Rabs_R1.
  simpl. rewrite Rabs_mult. rewrite IHn.
  rewrite Rmult_1_r. rewrite <- Rabs_Ropp.
  assert(- -1 = 1). { ring. } rewrite H.
  rewrite Rabs_R1; auto.
Qed.


Lemma pow_mult_ab : forall n a b, power n (a*b) = power n a * power n b.
Proof.
  intros.
  induction n. simpl. rewrite Rmult_1_l; auto.
  simpl. rewrite IHn. ring.
Qed.


(* Taylor公式的预备定理 *)
(*n阶可导，且n阶导数为f*)
Fixpoint N_str_derivative F f a b (n:nat) : Prop :=
  match n with
  | 0 => F = f
  | S p => exists f1, str_derivative F f1 a b /\ N_str_derivative f1 f a b p
  end.

(*n阶可导*)
Fixpoint N_str_derivability F a b (n:nat) : Prop :=
  match n with
  | 0 => N_str_derivative F F a b 0
  | S p => exists f, str_derivative F f a b /\ N_str_derivability f a b p
  end.


Corollary N_derivative_existence : forall a b n, forall F,
  N_str_derivability F a b n -> exists f, N_str_derivative F f a b n.
Proof.
  induction n; intros.
   - simpl in H. exists F; simpl; auto.
   - destruct H, H. apply IHn in H0. destruct H0.
     exists x0. exists x. split; auto.
Qed.

Corollary N0_derivative : forall F f a b,
  N_str_derivative F f a b 0 -> F = f.
Proof.
  simpl; auto.
Qed.

Axiom ex_trans :
  forall {A : Type} {P : A->Prop},
    (exists x, P x) -> { x : A | P x }.

Lemma der_F : forall {F a b}, str_derivability F a b -> 
  exists f, exists M, 0<M /\ forall x h:R, x ∈ [a,b] /\ (x+h) ∈ [a,b] ->
  Rabs (F(x+h) - F(x) - f(x)*h) <= M*(h^2).
Proof.
  intros; red in H; eauto.
Qed.


Definition Con_der {F a b} (l:str_derivability F a b) :=
  ex_trans (der_F l).


Definition Der {F a b}(l:str_derivability F a b) :=
  proj1_sig(Con_der l).


Definition Con_N_der {F a b n} (l:N_str_derivability F a b n) :=
  ex_trans (N_derivative_existence a b n F l).


Definition N_der {F a b n}(l:N_str_derivability F a b n) :=
  proj1_sig(Con_N_der l).


Definition N_der_pro {F a b n}(l:N_str_derivability F a b n) :=
  proj2_sig(Con_N_der l).


Corollary N0_der_eq: forall F a b (l:N_str_derivability F a b 0),
  N_der l = F.
Proof.
  intros; unfold N_der.
  destruct (Con_N_der l), n.
  simpl; auto.
Qed.


Section Taylor.

Lemma Nder_by_Snder : forall {F a b n}, N_str_derivability F a b (S n) ->
  N_str_derivability F a b n.
Proof.
  intros; generalize dependent  F; induction n; intros.
  - constructor.
  - destruct H, H. apply IHn in H0. exists x; auto.
Qed.

Lemma N_derivative_pro :forall F a b n, N_str_derivability F a b n ->
  forall k, (k<=n)%nat -> N_str_derivability F a b k.
Proof.
  intros; induction n.
  - assert (k = O). { apply Nat.le_0_r; auto. }
    rewrite H1. auto.
  - apply le_lt_or_eq in H0; destruct H0.
    apply  IHn. apply Nder_by_Snder; auto.
    apply lt_n_Sm_le; auto.
    rewrite <- H0 in H; auto.
Qed.


Lemma der_unique : forall {F f1 f2 a b}, str_derivative F f1 a b ->
  str_derivative F f2 a b -> f1 = f2.
Admitted.


Lemma Nder_unique : forall F f1 f2 a b n, N_str_derivative F f1 a b n ->
  N_str_derivative F f2 a b n -> f1 = f2.
Proof.
  intros; generalize dependent F; induction n; intros.
  - destruct H, H0; auto.
  - destruct H, H, H0, H0.
    pose proof (der_unique H H0); subst x.
    apply IHn with x0; auto.
Qed.

Lemma N_derivative_eq : forall F a b m n (p:N_str_derivability F a b m)
  (q:N_str_derivability F a b n), m = n -> N_der p = N_der q.
Proof.
  intros. subst m.
  unfold N_der; destruct (Con_N_der p), (Con_N_der q); simpl.
  eapply Nder_unique; eauto.
Qed.

Lemma N_sub_derivative : forall F a b m n (p:N_str_derivability F a b m)
  (q:N_str_derivability F a b n), S m = n ->
  str_derivative (N_der p) (N_der q) a b.
Proof.
  intros. subst n.
  unfold N_der; destruct (Con_N_der p), (Con_N_der q); simpl.
  clear p q. generalize dependent F.
  induction m; intros.
  - simpl in n, n0. destruct n0, H. subst F x1; auto.
  - destruct n, n0, H, H0.
    pose proof (der_unique H H0); subst x1.
    apply IHm with x2; auto.
Qed.


Theorem Taylor_Lemma H a b n (l: N_str_derivability H a b n) :
  (forall k (p:N_str_derivability H a b k), (k<n)%nat-> N_der p a = 0) ->
  forall m M, (forall x, x ∈ [a,b] -> m <= N_der l x <= M) -> 
  forall k , (k<=n)%nat -> forall x, x ∈ [a,b] ->
  forall q:N_str_derivability H a b (n-k),
  m*power k (x-a)/INR (factorial k) <= N_der q x <=
  M*power k (x-a)/ INR(factorial k).
Proof.
  intros H0 m M H1 k H2.
  induction k.
  - intros. unfold Rdiv.
    repeat rewrite Rinv_r_simpl_l; try apply R1_neq_R0.
    apply H1 in H3. rewrite N_derivative_eq with(n:=n)(q:=l); auto.
    rewrite Nat.sub_0_r; auto.
  - assert((k<=n)%nat) as le_k_n.
     { apply Nat.le_trans with (m:= S k); auto. }
    generalize(IHk le_k_n) as IHk_x; intros. clear IHk.
    assert(a<b) as lt_a_b. { destruct H3; auto. }
    generalize(power_inv_fac_der m a b k lt_a_b); intro.
    generalize(power_inv_fac_der M a b k lt_a_b); intro.
    assert(N_str_derivability H a b (n-k)) as p.
     { generalize(N_derivative_pro H a b n l (n-k)); intro.
       apply H6. apply Nat.le_sub_l. }
    assert(str_derivative (N_der q)(N_der p) a b).
     { assert((n-S k=n-k-1 /\ n-k=S(n-k-1))%nat).
        { split. auto.
          rewrite <- Nat.sub_add_distr. rewrite Nat.add_1_r; auto.
          rewrite <- Nat.add_1_r.
          rewrite Nat.sub_add; auto.
          apply plus_le_reg_l with (p:=k).
          rewrite Nat.add_comm with (m:=(n-k)%nat).
          rewrite Nat.sub_add. rewrite Nat.add_1_r; auto.
          apply Nat.le_trans with (m:=S k); auto. }
    apply N_sub_derivative. destruct H6.
    apply eq_S in H6. rewrite <- H7 in H6; auto. }
    assert(a<=x) as le_a_x.
     { unfold In in H3. unfold cc in H3. tauto. }
    split.
    + destruct le_a_x.
      * apply Theorem3_1_1' with (c:=-1) in H4.
        apply (Theorem3_1_2' _ _ _ _ _ _ H6) in H4.
        apply Theorem4_3 in H4. destruct H4. clear H8.
        unfold diff_quo_median in H4.
        assert(a ∈ [a, b] /\ x ∈ [a, b] /\ x - a > 0).
          { destruct H3, H8. repeat split; auto.
            apply Rle_refl. apply Rlt_le; auto.
            apply Rgt_minus; auto. }
        apply H4 in H8.
        destruct H8, H8, H8, H9, H10. clear H4 H11.
        unfold plus_Fu in H10; unfold mult_real_f in H10.
        assert(n-S k<n)%nat.
         { apply Nat.sub_lt; auto. apply Nat.lt_0_succ. }
        rewrite H0 in H10; auto.
        rewrite Rminus_diag_eq with(r1:=a) in H10; auto.
        rewrite Rplus_0_l in H10.
        assert(power (S k) 0 = 0).
         { simpl. rewrite Rmult_0_l; auto. }
        rewrite H11 in H10. rewrite Rmult_0_r in H10.
        unfold Rdiv in H10; rewrite Rmult_0_l in H10.
        rewrite Rmult_0_r in H10.
        assert(x0 ∈ [a, b]).
         { destruct H3, H12, H8, H14.
           split; auto. split; auto.
           apply Rle_trans with (r2:=x); auto. }
        apply IHk_x with(q:=p) in H12.
        apply Rplus_le_reg_r with 
          (r:=-(m*power(S k)(x-a)/INR(factorial(S k)))).
        rewrite Rplus_opp_r. destruct H12. clear H13.
        apply Rplus_le_compat_r with
          (r:=-(m*power k (x0-a)/INR(factorial k))) in H12.
        rewrite Rplus_opp_r in H12. unfold Rdiv in H12.
        repeat rewrite Ropp_mult_distr_l_reverse with (r1:=1)in H10.
        repeat rewrite Rmult_1_l in H10.
        apply Rle_trans with (r1:=0)in H10; auto.
        unfold Rdiv. rewrite Rminus_0_r in H10.
        apply Rmult_le_reg_r with (r:= / (x - a)).
        apply Rinv_0_lt_compat; apply Rlt_Rminus; auto.
        rewrite Rmult_0_l; auto.
      * rewrite <- H7. rewrite Rminus_diag_eq; auto.
        simpl. rewrite Rmult_0_l. rewrite Rmult_0_r.
        unfold Rdiv; rewrite Rmult_0_l.
        rewrite H0. apply Req_le; auto.
        apply Nat.sub_lt; auto.
        apply Nat.lt_0_succ.
    + destruct le_a_x.
      * apply Theorem3_1_1' with (c:=-1) in H5.
        apply (Theorem3_1_2' _ _ _ _ _ _ H6) in H5.
        apply Theorem4_3 in H5. destruct H5. clear H8.
        unfold diff_quo_median in H4.
        assert(a ∈ [a, b] /\ x ∈ [a, b] /\ x - a > 0).
          { destruct H3, H8. repeat split; auto.
            apply Rle_refl. apply Rlt_le; auto.
            apply Rgt_minus; auto. }
        apply H5 in H8.
        destruct H8, H8, H8, H9, H10. clear H5 H10.
        unfold plus_Fu in H11; unfold mult_real_f in H11.
        assert(n-S k<n)%nat.
         { apply Nat.sub_lt; auto. apply Nat.lt_0_succ. }
        rewrite H0 in H11; auto.
        rewrite Rminus_diag_eq with(r1:=a) in H11; auto.
        rewrite Rplus_0_l in H11.
        assert(power (S k) 0 = 0).
         { simpl. rewrite Rmult_0_l; auto. }
        rewrite H10 in H11. rewrite Rmult_0_r in H11.
        unfold Rdiv in H11; rewrite Rmult_0_l in H11.
        rewrite Rmult_0_r in H11.
        assert(x1 ∈ [a, b]).
         { destruct H3, H12, H9, H14.
           split; auto. split; auto.
           apply Rle_trans with (r2:=x); auto. }
        apply IHk_x with(q:=p) in H12.
        apply Rplus_le_reg_r with 
          (r:=-(M*power(S k)(x-a)/INR(factorial(S k)))).
        rewrite Rplus_opp_r. destruct H12. clear H12.
        apply Rplus_le_compat_r with 
          (r:=-(M*power k (x1-a)/INR(factorial k))) in H13.
        rewrite Rplus_opp_r in H13. unfold Rdiv in H13.
        repeat rewrite Ropp_mult_distr_l_reverse with (r1:=1)in H11.
        repeat rewrite Rmult_1_l in H11.
        apply Rle_trans with (r3:=0)in H11; auto.
        unfold Rdiv. rewrite Rminus_0_r in H11.
        apply Rmult_le_reg_r with (r:= / (x - a)).
        apply Rinv_0_lt_compat; apply Rlt_Rminus; auto.
        rewrite Rmult_0_l; auto.
      * rewrite <- H7. rewrite Rminus_diag_eq; auto.
        simpl. rewrite Rmult_0_l. rewrite Rmult_0_r.
        unfold Rdiv; rewrite Rmult_0_l.
        rewrite H0. apply Req_le; auto.
        apply Nat.sub_lt; auto.
        apply Nat.lt_0_succ.
Qed.


Variable Nder_H: forall {H a b n}, N_str_derivability H a b n.

Lemma Nder_H' : forall H a b n, N_str_derivative H (N_der(Nder_H H a b n)) a b n.
Proof.
  intros. unfold N_der. destruct Con_N_der.
  simpl. auto.
Qed.

Lemma N_der_eq : forall {H f1 f2 a b n}, N_str_derivative H f1 a b n ->
  N_str_derivative H f2 a b n -> f1 = f2.
Proof.
  intros. generalize dependent H.
  induction n.
  - intros. simpl in H0, H1. 
    rewrite <- H0, H1; auto.
  - intros. simpl in H0, H1.
    destruct H0, H0, H1, H1.
    generalize(der_unique H0 H1); intro.
    rewrite <- H4 in H3.
    apply IHn with (H:=x); auto.
Qed.

Fixpoint Taylor_Formula H a b n (x c:R)  :=
  match n with
  | 0 => 0
  | S p => ((N_der (Nder_H H a b p)) c)*(power p (x-c))/INR(factorial p)+
           Taylor_Formula H a b p x c
  end.

Lemma lt_ge_dec : forall n m : nat, {(n < m)%nat} + {(n >= m)%nat}.
Proof.
  intros. generalize (le_gt_dec m n); intro.
  destruct H; auto.
Qed.

Fixpoint Taylor_FormulaDer H a b n x c k  := 
  match n with 
  | 0 => 0
  | S p => match lt_ge_dec k n with
           |left _ => ((N_der (Nder_H H a b p)) c)*(power (p-k) (x-c))/INR(factorial (p-k)) +
                      (Taylor_FormulaDer H a b p x c k)
           |right _ => 0
                 end
  end.

Variable fun_eq : forall (f1 f2:R->R), (forall a, f1 a = f2 a) <-> f1 = f2.

Lemma Str_Plus_FG : forall F G (a b:R),
  str_derivability F a b -> str_derivability G a b ->
  str_derivability (plus_Fu F G) a b.
Proof.
  intros.
  destruct H, H, H. rename x0 into M1. rename x into f.
  destruct H0, H0, H0. rename x0 into M2. rename x into g.
  exists (plus_Fu f g), (M1+M2). split.
  apply Rplus_lt_0_compat; auto. intros.
  generalize H3; intro.
  apply H2 in H3; apply H1 in H4. unfold plus_Fu. 
  rewrite Rmult_plus_distr_r with (r1:=(f x))(r2:=(g x))(r3:=h).
    rewrite plus_ab_minus_cd with (a:=F(x+h))(b:=G(x+h))(c:=F x)
                                  (d:=G x)(e:=f x*h)(f:=g x*h).
    assert (Rabs(F(x+h) - F x - f x*h)+Rabs(G(x+h) - G x - g x*h)
            <= (M1+M2) * h ^ 2).
     { rewrite Rmult_plus_distr_r. 
       apply Rplus_le_compat; auto. }
    apply Rle_abcd with (a:=Rabs(F(x+h)-F x-f x*h+(G(x+h)-G x-g x*h)))
                        (b:=Rabs(F(x+h)-F x-f x*h)+Rabs(G(x+h)-G x-g x*h))
                        (c:=M1*h^2+M2*h^2)
                        (d:=(M1+M2)*h^2).
    + apply Rabs_triang.
    + rewrite Rmult_plus_distr_r.
      apply Rle_refl.
    + rewrite <-Rmult_plus_distr_r; auto.
Qed.


Lemma plus_FG_Nder n : forall F G a b, N_str_derivability F a b n ->
  N_str_derivability G a b n ->
  N_str_derivability (plus_Fu F G) a b n.
Proof.
  induction n.
  - intros. simpl; auto. 
  - intros. simpl. simpl in H; simpl in H0.
    destruct H, H, H0, H0. rename x into f. rename x0 into g.
    exists(plus_Fu f g).
    split.
    + apply Theorem3_1_2'; auto.
    + apply IHn with (G:=g) in H1; auto.
Qed.


Lemma plus_FG_Nder' n : forall F f G g a b, N_str_derivative F f a b n ->
  N_str_derivative G g a b n ->
  N_str_derivative (plus_Fu F G) (plus_Fu f g) a b n.
Proof.
  induction n.
  - intros. simpl; auto. simpl in H; simpl in H0.
    rewrite H; rewrite H0; auto.
  - intros. simpl. simpl in H; simpl in H0.
    destruct H, H, H0, H0. rename x into f1. rename x0 into g1.
    exists(plus_Fu f1 g1).
    split.
    + apply Theorem3_1_2'; auto.
    + apply (IHn f1 f g1 g a b) in H1; auto.
Qed.


Lemma Sn_der : forall H f1 f2 a b n, N_str_derivative H f1 a b n ->
  str_derivative f1 f2 a b -> N_str_derivative H f2 a b (S n).
Proof.
  intros. generalize dependent H; induction n; intros.
  - simpl in H0. subst H. simpl. exists f2; auto.
  - simpl in H0. destruct H0 as [h1 [H0]].
    apply IHn in H2. exists h1; auto.
Qed.


Lemma Strder_fun0 : forall a b, str_derivative (fun _ => 0) (fun _ => 0) a b.
Proof.
  intros; red.
  exists 1.
  split. apply Rlt_0_1.
  intros.
  rewrite Rmult_0_l. repeat rewrite Rminus_0_r.
  rewrite Rmult_1_l. rewrite Rabs_R0.
  apply pow2_ge_0.
Qed.

Lemma Str_Snder : forall H f1 f2 a b n, N_str_derivative H f1 a b n -> 
  N_str_derivative H f2 a b (S n) -> str_derivative f1 f2 a b .
Proof.
  intros. generalize dependent H; induction n; intros.
  - simpl in H0, H1. destruct H0, H1, H0. subst x; auto.
  - destruct H0, H1, H0, H1.
    pose proof (der_unique H0 H1); subst x.
    apply IHn with x0; auto.
Qed.

Lemma Domain_Strder : forall f f1 a b c, c ∈ [a, b] -> str_derivative f f1 a b -> str_derivative f f1 c b.
Proof.
  intros. red in H0|-*.
  destruct H0 as [M [H0]].
  exists M. split; auto. intros.
  apply H1. destruct H2, H2, H3, H, H6, H4, H5.
  repeat split; auto; try apply Rle_trans with(r2:=c); auto.
Qed.


Lemma Domain_Nder F a b c n : c ∈ [a, b] -> N_str_derivability F a b n ->
  N_str_derivability F c b n.
Proof.
  intros. generalize dependent F; induction n; auto.
Qed.


Lemma Domain_Nder' F f a b c n : c ∈ [a, b] -> N_str_derivative F f a b n ->
  N_str_derivative F f c b n.
Proof.
  intros. generalize dependent F; induction n; auto.
  intros. simpl in H0|-*.
  destruct H0 as [f1 [H0]].
  exists f1; split; auto.
  eapply Domain_Strder; eauto.
Qed.


Lemma Domain_Nder_eq : forall {f a b c n}, c ∈ [a, b] -> (N_der (Nder_H f a b n)) = (N_der (Nder_H f c b n)).
Proof.
  intros. unfold N_der. 
   destruct (Con_N_der (Nder_H f a b n)), (Con_N_der (Nder_H f c b n)); simpl.
  generalize dependent f; induction n; intros.
  - simpl in n0, n1. subst f; auto.
  - destruct n0, n1, H0, H1.
    pose proof (Domain_Strder _ _ _ _ _ H H0).
    pose proof (der_unique H1 H4). subst x2.
    apply IHn with x1; auto.
Qed.

Lemma Domain_Taylor_eq : forall f a b c n d, c ∈ [a, b] ->
  (fun x => Taylor_Formula f a b n x d) = (fun x => Taylor_Formula f c b n x d).
Proof.
  intros. apply fun_eq; intros.
  induction n; auto.
  - simpl. rewrite IHn. erewrite Domain_Nder_eq; eauto.
Qed.

Lemma Domain_Taylor_Nder_eq : forall f a b c n d k, c ∈ [a, b] -> 
  (fun x => Taylor_FormulaDer f a b n x d k) = (fun x => Taylor_FormulaDer f c b n x d k).
Proof.
  intros. apply fun_eq; intros.
  induction n; auto.
  - simpl. rewrite IHn. erewrite Domain_Nder_eq; eauto.
Qed.


Lemma Nder_power_inv_fac : forall a b p n k,  (k <= n)%nat -> a<b ->
  N_str_derivative (fun x : R => p * power n (x - a) / INR (factorial n))
  (fun x : R => p * power (n - k) (x - a) / INR (factorial (n - k))) a b k.
Proof.
  intros. induction k. 
  - simpl. rewrite <- minus_n_O; auto.
  - assert (str_derivative  (fun x : R => p * power (n - k) (x - a) / INR (factorial (n - k)))
      (fun x : R => p * power (n - S k) (x - a) / INR (factorial (n - S k))) a b).
    { assert (n-k = S (n - (S k)))%nat.
      { rewrite Nat.sub_succ_r, Nat.succ_pred_pos; auto.
         apply lt_minus_O_lt; apply  le_S_gt; auto. }
      rewrite H1. eapply power_inv_fac_der with (a:=a)(b:=b); auto. }
    apply le_Sn_le in H. eapply Sn_der; eauto.
Qed.


Lemma Rminus_refl : forall n, n - n =0.
Proof.
  intros. apply Rminus_diag_eq; auto.
Qed.

Lemma Nder_Taylor_eq0 : forall H a b n, a<b -> N_str_derivative (fun x : R => Taylor_Formula H a b n x a)
 (fun x : R => 0) a b n.
Proof.
  intros. induction n.
  - simpl; auto.
  - simpl Taylor_Formula.
    assert((fun _ => 0) = plus_Fu (fun _ => 0) (fun _ => 0)) as pp.
    { unfold plus_Fu. rewrite Rplus_0_r; auto. } rewrite pp.
    apply plus_FG_Nder'.
    * pose proof (Nat.le_refl n).
    pose proof (Nder_power_inv_fac a b (N_der (Nder_H H a b n) a) n n H1).
    rewrite Nat.sub_diag in H2; simpl in H2.
    unfold Rdiv in H2; rewrite Rmult_1_r, RMicromega.Rinv_1 in H2.
    assert (str_derivative  (fun _ : R => N_der (Nder_H H a b n) a) (fun _ : R => 0) a b).
     { exists 1.
       split. apply Rlt_0_1.
       intros. rewrite Rmult_0_l. rewrite Rminus_0_r.
       rewrite Rminus_refl. rewrite Rabs_R0. rewrite Rmult_1_l.
       apply pow2_ge_0. }
    eapply Sn_der; eauto.
    * pose proof (Strder_fun0 a b). eapply Sn_der; eauto.
Qed.


Lemma Taylor_onC_eq0 : forall H a b c n x,  Taylor_FormulaDer H a b n x c n = 0.
Proof.
  intros. induction n. simpl; auto.
  simpl. destruct (lt_ge_dec (S n) (S n)); auto.
  apply Nat.lt_irrefl in l. destruct l.
Qed.

Lemma Taylor_Nder': forall H a b n k, (k < n)%nat -> a<b ->
  N_str_derivative (fun x => Taylor_Formula H a b n x a)
  (fun x => (Taylor_FormulaDer H a b n x a k)) a b k.
Proof.
  intros. generalize dependent k;
  induction n; simpl;intros. induction k. simpl. auto.
  exists  (fun _ : R => 0). split;
  apply Nat.nlt_0_r in H0; contradiction.
  induction k. simpl. simpl in IHn. destruct (lt_ge_dec 0 (S n)).
  rewrite Nat.sub_0_r.
  assert(forall f1 f2, (fun x => (f1 x + f2 x)) = plus_Fu (fun x => f1 x) (fun x => f2 x)) as pp. { auto. }
  repeat rewrite pp. f_equal.
  specialize IHn with O.
  assert (n=O \/ n > O)%nat. 
  { apply lt_n_Sm_le in l. destruct l.
    left; auto.
    right. apply le_lt_n_Sm; auto. }
  destruct H2.
  subst n; simpl; auto.  simpl in IHn; auto.
  apply lt_not_le in H0. contradiction.
  destruct (lt_ge_dec (S k) (S n)).
  destruct (lt_ge_dec k (S n)).
  apply IHk in l0. clear IHk. apply lt_S_n in H0.
  repeat rewrite pp. apply plus_FG_Nder'; auto.
  apply Nder_power_inv_fac; auto.
  assert (S k=n \/ S k < n)%nat.
   { apply lt_n_Sm_le in l. destruct l.
     left; auto.
     right; apply le_lt_n_Sm; auto. }
  { destruct H2.
    - rewrite H2.
    assert ((fun x : R => Taylor_FormulaDer H a b n x a n)  = (fun x : R => 0)). 
     { apply fun_eq; intros; rewrite Taylor_onC_eq0; auto. }
    rewrite H3. apply Nder_Taylor_eq0; auto.
    - apply IHn; auto. }
  apply le_S_gt in g. apply gt_n_S in g.
  apply gt_asym in g. contradiction.
  apply lt_not_le in H0. contradiction.
Qed.


Lemma Taylor_FormulaDer_onC H a b n c: forall k, (k<n)%nat ->
  Taylor_FormulaDer H a b n c c k = N_der (Nder_H H a b k) c.
Proof.
  intros.
  revert H0.
  induction n; intros.
  - apply Nat.nlt_0_r in H0; contradiction.
  - assert (k=n \/ (k < n)%nat). 
     { apply lt_n_Sm_le in H0. destruct H0.
       left; auto. 
       right; apply le_lt_n_Sm; auto. } destruct H1.
    subst k. simpl Taylor_FormulaDer.
    rewrite <- minus_diag_reverse.
    destruct (lt_ge_dec n (S n)).
    rewrite Rminus_diag_eq; auto. simpl.
    rewrite Rmult_1_r. unfold Rdiv. rewrite Rinv_1, Rmult_1_r.
    rewrite Taylor_onC_eq0. apply Rplus_0_r.
    apply lt_not_le in H0; contradiction.
    simpl. destruct (lt_ge_dec k (S n)); auto.
    rewrite Rminus_diag_eq; auto.
    assert(forall n:nat, (0<n)%nat -> power n 0 = 0) as power_0.
     { intros. induction n0. apply Nat.lt_irrefl in H2. contradiction. 
       simpl. rewrite Rmult_0_l; auto. }
    assert(forall (n m:nat),  (n<=m) -> n<m\/n=m)%nat as or_lt_eq .
     { intros. destruct H2.
       right; auto.
       left. apply le_lt_n_Sm; auto. }
    rewrite power_0. rewrite Rmult_0_r. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rplus_0_l. apply IHn. auto.
    apply lt_minus_O_lt; auto.
    apply lt_not_le in H0; contradiction.
Qed.

Lemma Nder_opp : forall f a b n, N_str_derivability f a b n ->
  N_str_derivability (fun x => - (f x)) a b n.
Proof.
  intros; generalize dependent f; induction n; intros.
  - simpl; auto.
  - simpl. destruct H, H. apply IHn in H0.
    exists (fun x0 : R => - x x0); split; auto.
    destruct H, H; red.
    exists x0; split; intros; auto.
    apply H1 in H2. 
    rewrite <- Rabs_Ropp in H2.
    unfold Rminus in H2. repeat rewrite Ropp_plus_distr, Ropp_involutive in H2.
    unfold Rminus; rewrite Ropp_involutive, Ropp_mult_distr_l, Ropp_involutive; auto.
Qed.

Lemma Nder_opp' : forall F f a b n, N_str_derivative F f a b n ->
  N_str_derivative (fun x => - (F x)) (fun x => - (f x)) a b n.
Proof.
  intros; generalize dependent F; induction n; intros.
  - simpl in H. simpl; rewrite H; auto.
  - simpl. destruct H, H. apply IHn in H0.
    exists (fun x0 : R => - x x0); split; auto.
    destruct H, H; red.
    exists x0; split; intros; auto.
    apply H1 in H2. 
    rewrite <- Rabs_Ropp in H2.
    unfold Rminus in H2. repeat rewrite Ropp_plus_distr, Ropp_involutive in H2.
    unfold Rminus; rewrite Ropp_involutive, Ropp_mult_distr_l, Ropp_involutive; auto.
Qed.


Lemma Taylor_Nder: forall H a b n, a<b ->
  N_str_derivability (fun x => Taylor_Formula H a b n x a) a b n.
Proof.
  intros.
  generalize(Nder_Taylor_eq0 H a b n); intro.
  induction n.
  - simpl; auto.
  - simpl. apply H1 in H0. simpl in H0.
    destruct H0, H0. exists x.
    split; auto.
Qed.


Lemma Taylor_on_cb : forall H a b n (l: N_str_derivability H a b n) M, 
  (forall x, x ∈ [a, b] -> Rabs(N_der l x)<=M) ->
  forall c x, c ∈ [a, b] -> x ∈ [c, b] -> 
  Rabs(H(x)-(Taylor_Formula H a b n x c))<=
  M*Rabs(power n (x-c))/INR(factorial n).
Proof.
  intros.
  assert (x ∈ [a, b]) as Domain_x. 
   { destruct H1, H3, H2, H5.
     repeat split; auto.
     apply Rle_trans with (r2:=c); auto. }
  generalize H1 as Domain_c; intro.
  assert(forall k, (k<n)%nat -> N_str_derivative
    (fun x : R => H x - Taylor_Formula H a b n x c)
    (fun x : R => N_der (Nder_H H a b k) x - (Taylor_FormulaDer H a b n x c k)) c b k) as N_der_Taylor.
   { intros. unfold Rminus.
     apply plus_FG_Nder'. apply Domain_Nder' with (a:=a)(b:=b).
     apply Domain_c. apply Nder_H'.
     apply Nder_opp'.
     rewrite Domain_Taylor_eq with (c:=c); auto.
     rewrite Domain_Taylor_Nder_eq with (c:=c); auto. apply Taylor_Nder'; auto.
     destruct H2; auto. }
  assert(N_str_derivative (fun x : R => H x - Taylor_Formula H a b n x c)
    (fun x : R => N_der (Nder_H H a b n) x - 0) c b n) as N_der_Taylor_onN.
   { intros. unfold Rminus.
     apply plus_FG_Nder'. apply Domain_Nder' with (a:=a)(b:=b).
     apply Domain_c. apply Nder_H'.
     apply Domain_Nder' with (a:=c)(b:=b).
     destruct H2. repeat split; auto. apply Rle_refl. apply Rlt_le; auto.
     apply Nder_opp'. rewrite Domain_Taylor_eq with (c:=c); auto. apply Nder_Taylor_eq0; auto.
     destruct H2; auto. }
    apply Rabs_le.
    rewrite Rabs_pos_eq; try apply power_x_pos.
    assert(-(M*power n (x-c)/INR(factorial n))=
            -M*power n (x-c)/INR(factorial n)).
     { unfold Rdiv. repeat rewrite Rmult_assoc.
       rewrite Ropp_mult_distr_l; auto. }
    rewrite H3. clear H3.
    assert(N_str_derivability (fun x => H x-Taylor_Formula H a b n x c) c b 0).
     { simpl. auto. }
    assert(forall (f g:R->R) x, f = g -> f x = g x).
     { intros. rewrite H4; auto. }
    assert(N_der H3 x = H x-Taylor_Formula H a b n x c).
     { unfold N_der. unfold Con_N_der. 
       generalize(ex_trans (N_derivative_existence c b 0
        (fun x0 : R => H x0 - Taylor_Formula H a b n x0 c) H3)); intro.
       generalize(proj2_sig s); intro. simpl in H5.
       apply H4 with (g:=(fun x0 : R => H x0 - Taylor_Formula H a b n x0 c)); auto. }
    assert(n-n=0)%nat. { apply Nat.sub_diag. }
    generalize H3; auto; intro. rewrite <- H6 in H7.
    generalize (N_derivative_eq _ _ _ 0 (n-n) H3 H7); intro.
    rewrite <- H5. rewrite H4 with(f:=N_der H3)(g:=N_der H7); auto.
    assert(N_str_derivability (fun x =>H x - Taylor_Formula H a b n x c) c b n).
     { unfold Rminus.
       apply plus_FG_Nder. apply Domain_Nder with (a:=a)(b:=b).
       apply Domain_c. apply l.
       apply Domain_Nder with (a:=c)(b:=b).
       destruct H2. repeat split; auto.
       apply Rle_refl. apply Rlt_le; auto.
       apply Nder_opp. rewrite Domain_Taylor_eq with (c:=c); auto. }
    apply Taylor_Lemma with(l:=H9)(H:=(fun x : R => H x - Taylor_Formula H a b n x c))
      (a:=c)(b:=b)(m:=-M)(q:=H7)(x:=x)(n:=n)(k:=n)(M:=M); auto.
    + intros.
      unfold N_der. destruct (Con_N_der p). simpl.
      generalize(N_der_eq n0 (N_der_Taylor k H10)); intro.
      rewrite H11.
      rewrite Taylor_FormulaDer_onC; auto.
      apply Rminus_diag_eq; auto.
    + intros.
      assert(x0 ∈ [a, b]) as Domain_c_x0.
       { destruct Domain_c. destruct H10, H12, H13.
         repeat split; auto.
         apply Rle_trans with (r2:=c); auto. }
      generalize(N_der_Taylor_onN); intro.
      generalize(Nder_H' (fun x : R => H x - Taylor_Formula H a b n x c) c b n); intro.
      generalize(N_der_eq N_der_Taylor_onN0 H11); intro.
      assert((fun x : R => N_der (Nder_H H a b n) x - 0) = (fun x : R => N_der (Nder_H H a b n) x)).
        { apply fun_eq. intro.
          rewrite Rminus_0_r; auto. }
      rewrite H13 in H12.
      generalize(N_derivative_eq (fun x : R => H x - Taylor_Formula H a b n x c) c b n n
      H9 (Nder_H (fun x : R => H x - Taylor_Formula H a b n x c) c b n)); intro.
      rewrite H14; auto. rewrite <- H12.
      apply Rabs_le_reg.
      generalize( N_derivative_eq H a b n n l (Nder_H H a b n)); intro.
      rewrite <- H15; auto.
    + destruct H1, H3. apply Rge_le; apply Rge_minus.
      apply Rle_ge; auto.
      destruct H2, H5; auto.
Qed.


Lemma Nder_leN_exist : forall H f1 a b n, N_str_derivative H f1 a b (S n) ->forall k, (k<=n)%nat->
 exists f2, N_str_derivative H f2 a b k.
Proof.
  intros; apply N_derivative_existence; eapply N_derivative_pro; eauto.
Qed.


Lemma Taylor_opp_on_cb : forall {H f1 f2 a b n}, N_str_derivative H f1 a b n -> N_str_derivative (fun x => H (- x)) f2 (-b) (-a) n
  -> f2 = (fun x => (power n (-1)) * (f1 (- x))).
Proof.
  intros. generalize dependent f1; generalize dependent f2; induction n; intros.
  - simpl. simpl in H0, H1. rewrite <- H1, H0.
    apply fun_eq; intros. rewrite Rmult_1_l; auto.
  - assert (exists f11, N_str_derivative H f11 a b n).
     { apply Nder_leN_exist with (k:=n) in H0; auto. }
    assert (exists f22, N_str_derivative (fun x : R => H (- x)) f22 (-b) (-a) n).
     { apply Nder_leN_exist with (k:=n) in H1; auto. }
    destruct H2 as [f11 H2]. destruct H3 as [f22 H3].
    pose proof (IHn _ H3 _ H2).
    assert (str_derivative f11 f1 a b).
    { apply Str_Snder with (H:=H)(n:=n); auto. }
    assert (str_derivative f22 f2 (-b) (-a)).
     { apply Str_Snder with (H:=fun x : R => H (- x))(n:=n); auto. }
    assert (str_derivative (fun x => f11 (-x)) (fun x => - (f1 (-x))) (-b) (-a)).
    { clear H6. destruct H5, H5. rename x into M.
      exists M. split; auto.
      intros.
      assert( (-x) ∈ [a, b] /\ (-x + -h) ∈ [a, b]).
       { split. destruct H7.
         - destruct H7, H9.
           repeat split. apply Ropp_lt_cancel; auto.
           rewrite <- Ropp_involutive with (r:=x) in H10.
           apply Ropp_le_cancel in H10; auto.
           rewrite <- Ropp_involutive with (r:=x) in H9.
           apply Ropp_le_cancel in H9; auto.
         - destruct H7, H8, H9.
           repeat split. apply Ropp_lt_cancel; auto.
           rewrite <- Ropp_plus_distr.
           rewrite <- Ropp_involutive with (r:=x+h) in H10.
           apply Ropp_le_cancel in H10; auto.
           rewrite <- Ropp_plus_distr.
           rewrite <- Ropp_involutive with (r:=x+h) in H9.
           apply Ropp_le_cancel in H9; auto.  }
      apply H6 in H8.  rewrite <- Ropp_plus_distr in H8.
        unfold Rminus. unfold Rminus in H8.
        rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_comm in H8. rewrite Ropp_mult_distr_l_reverse in H8.
        rewrite Rmult_comm; auto.
        rewrite <- Rsqr_pow2. rewrite <- Rsqr_pow2 in H8.
        rewrite Rsqr_neg; auto. }
    assert(str_derivative (fun x : R => power n (-1) * f11 (- x))
      (fun x => power n (-1) * (- (f1 (-x)))) (-b) (-a)).
     { apply Theorem3_1_1'; auto. }
    rewrite H4 in H6.
    pose proof (der_unique H6 H8).
    rewrite H9. simpl.
    apply fun_eq. intro. ring.
Qed.


Theorem Taylor_Theorem H a b n (l: N_str_derivability H a b n):
  forall M, (forall x, x ∈ [a, b] -> Rabs(N_der l x)<=M) ->
  forall c x, c ∈ [a, b] -> x ∈ [a, b] -> 
  Rabs(H(x)-(Taylor_Formula H a b n x c))<=
  M*Rabs(power n (x-c))/INR(factorial n).
Proof.
  intros.
  generalize H2 as Domain_x; intro.
  generalize H1 as Domain_c; intro.
  apply Domain_x_c with (x:=x) in H1; auto.
  destruct H1.
  - eapply Taylor_on_cb; eauto.
  - set (u:=-x).
    assert(x = -u). { unfold u. ring. }
    rewrite H3.
    set (G := fun u => H (- u) ).
    assert (Rabs(G(u)-(Taylor_Formula G (-b) (-a) n u (-c)))<= M*Rabs(power n (u-(-c)))/INR(factorial n)).
    { assert (N_str_derivability G (-b) (-a) n).
      { unfold G. clear H0. generalize dependent H. induction n; intros. simpl; auto.
        simpl. simpl in l. destruct l as [f [H0]].
        exists (fun x => - (f (-x))); split.
        destruct H0 as [M1 [H0]].
        exists M1; split ;auto. intros.
        assert ((-x0) ∈ [a, b] /\ ((-x0) + (-h)) ∈ [a, b]). 
         { split. destruct H6.
           - destruct H6, H8.
             repeat split. apply Ropp_lt_cancel; auto.
             rewrite <- Ropp_involutive with (r:=x0) in H9.
             apply Ropp_le_cancel in H9; auto.
             rewrite <- Ropp_involutive with (r:=x0) in H8.
             apply Ropp_le_cancel in H8; auto.
           - destruct H6, H7, H8.
             repeat split. apply Ropp_lt_cancel; auto.
             rewrite <- Ropp_plus_distr.
             rewrite <- Ropp_involutive with (r:=x0+h) in H9.
             apply Ropp_le_cancel in H9; auto.
             rewrite <- Ropp_plus_distr.
             rewrite <- Ropp_involutive with (r:=x0+h) in H8.
             apply Ropp_le_cancel in H8; auto. }
        apply H5 in H7.
        rewrite <- Ropp_plus_distr in H7.
        unfold Rminus. unfold Rminus in H7.
        rewrite Ropp_mult_distr_l_reverse.
        rewrite Rmult_comm in H7. rewrite Ropp_mult_distr_l_reverse in H7.
        rewrite Rmult_comm; auto.
        rewrite <- Rsqr_pow2. rewrite <- Rsqr_pow2 in H7.
        rewrite Rsqr_neg; auto.
        apply IHn in H4; auto. }
       apply (Taylor_on_cb G (-b) (-a) n H4).
       intros.
       assert ((-x0) ∈ [a, b]). 
        { destruct H5, H6.
          repeat split. apply Ropp_lt_cancel; auto.
          rewrite <- Ropp_involutive with (r:=x0) in H7.
          apply Ropp_le_cancel in H7; auto.
          rewrite <- Ropp_involutive with (r:=x0) in H6.
          apply Ropp_le_cancel in H6; auto.  }
       apply H0 in H6.
       assert (Rabs (N_der l (- x0)) = Rabs (N_der H4 x0)).
       { unfold N_der. destruct (Con_N_der l), (Con_N_der H4); simpl.
          rename x1 into f1. rename x2 into f2.
          pose proof (Taylor_opp_on_cb n0 n1). rewrite H7.
          rewrite Rabs_mult. rewrite Rabs_power_opp.
          rewrite Rmult_1_l; auto. }
    rewrite <- H7; auto.
    destruct Domain_c, H6. repeat split.
    try apply Ropp_lt_contravar; auto.
    apply Ropp_le_contravar; auto.
    apply Ropp_le_contravar; auto.
    apply Ropp_eq_compat in H3. rewrite Ropp_involutive in H3.
    rewrite <- H3. destruct H1, H5.
    repeat split.
    try apply Ropp_lt_contravar; auto.
    apply Ropp_le_contravar; auto.
    apply Ropp_le_contravar; auto. }
    assert (Taylor_Formula G (- b) (- a) n u (- c) = Taylor_Formula H a b n (- u) c).
    { unfold G. clear H0 l H4.  induction n. simpl. auto. 
      simpl. rewrite IHn. f_equal. f_equal.
      assert (N_str_derivative H (N_der (Nder_H H a b n)) a b n).
      { unfold N_der; destruct ((Con_N_der (Nder_H H a b n))); simpl; auto. }
      assert (N_str_derivative (fun u0 => H (- u0)) (N_der (Nder_H (fun u0 => H (- u0)) (- b) (- a) n)) (-b) (-a) n).
      { unfold N_der; destruct ((Con_N_der (Nder_H (fun u0 => H (- u0)) (- b) (- a) n))); simpl; auto. }
      pose proof (Taylor_opp_on_cb H0 H4).
      rewrite H5. unfold Rminus; rewrite Ropp_involutive.
      assert(-u + -c = -1*(u+c)). { ring. }
      rewrite H6. rewrite pow_mult_ab.
      rewrite Rmult_comm with (r1:=N_der (Nder_H H a b n) c).
      rewrite Rmult_assoc. rewrite Rmult_comm with (r1:=N_der (Nder_H H a b n) c).
      rewrite <- Rmult_assoc; auto. }
    rewrite <- H5. unfold Rminus in H4. rewrite Ropp_involutive in H4.
    unfold Rminus.
    assert(Rabs (power n (- u + - c)) = Rabs (power n (u + c))).
     { assert(-u + -c = -1*(u+c)). { ring. }
       rewrite H6. rewrite pow_mult_ab. rewrite Rabs_mult.
       rewrite Rabs_power_opp. rewrite Rmult_1_l; auto.  }
    rewrite H6; auto.
Qed.