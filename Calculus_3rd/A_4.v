Require Export A_3.
Require Import Rlogic.

(*F(x)的差商为f(x)的中值*)
Definition diff_quo_median F f a b :=
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 ->
  exists (p q:R), p ∈ [u,v] /\ q ∈ [u,v] /\ f p <= (F v - F u)/(v - u) <= f q.

Theorem Theorem4_1_1 : forall (S: R->R->R) (f F:R->R) (a b:R),
  integ_sys S f a b ->
  strict_unequal S f a b ->
  forall y, y ∈ [a,b] ->(forall x, x ∈ [a,b] -> F x = S y x) ->
  diff_quo_median F f a b.
Proof.
  intros.
  unfold diff_quo_median; intros.
  destruct H0 with (w1:=u)(w2:=v); auto.
  generalize (Valuation_Theorem S f F a b ); intros.
  apply H6 with (y:=y)(u:=u)(v:=v)in H; auto; clear H6.
  destruct H, H, H, H6.
  exists x, x0.
  split; auto. split; auto.
  destruct H3, H8, H7.
  split;
  apply Rmult_le_reg_r with (r:=v-u); auto;
  unfold Rdiv; rewrite Rinv_mult_rgt0 with (r:=(v-u))(r1:=F v - F u); auto.
Qed.


Theorem Theorem4_1_2 : forall (S: R->R->R) (f F:R->R) (a b:R),
  (forall u v, u ∈ [a,b] /\ v ∈ [a,b] -> S u v = F v - F u) ->
  diff_quo_median F f a b ->
  integ_sys S f a b /\ strict_unequal S f a b.
Proof.
 intros.
 unfold diff_quo_median in H0.
 split.
 - unfold integ_sys.
   split.
   + unfold additivity; intros.
     generalize (H w1 w2); intros; rewrite H2.
     generalize (H w2 w3); intros; rewrite H3.
     generalize (H w1 w3); intros; rewrite H4.
     ring. tauto. tauto. tauto.
   + unfold nonnegativity; intros.
     generalize H1; intro.
     apply H0 in H1; auto; clear H0.
     destruct H1, H0, H0, H1, H3.
     split; intros.
      * apply H5 in H0; clear H5.
        apply Rmult_le_reg_r with (r:=/(w2 - w1)).
        apply Rinv_0_lt_compat; tauto.
        rewrite Rinv_r_simpl_l. rewrite H.
        eapply Rle_trans. apply H0. apply H3. tauto.
        apply Rgt_not_eq; tauto.
      * apply H5 in H1; clear H5.
        apply Rmult_le_reg_r with (r:=/(w2 - w1)).
        apply Rinv_0_lt_compat; tauto.
        rewrite Rinv_r_simpl_l. rewrite H.
        eapply Rle_trans. apply H4. apply Rge_le; auto. tauto.
        apply Rgt_not_eq; tauto.
  - unfold strict_unequal; intros.
    generalize H2 as l; intro.
    apply H0 in H2; clear H0; rewrite H.
    destruct H2, H0, H0, H2, H3.
    split; intros.
    + apply Rmult_lt_reg_r with (r:= /(w2 - w1)).
      apply Rinv_0_lt_compat. tauto.
      rewrite Rinv_r_simpl_l.
      eapply Rlt_le_trans. apply H5. apply H0. auto.
      apply Rgt_not_eq; tauto.
    + apply Rmult_lt_reg_r with (r:= /(w2 - w1)).
      apply Rinv_0_lt_compat. tauto.
      rewrite Rinv_r_simpl_l.
      eapply Rle_lt_trans. apply H4. apply H5; auto.
      apply Rgt_not_eq; tauto.
    + tauto.
Qed.

(*定义4.2*)
(*可加性*)
Definition additivity' (S:R->R->R)(a b:R):=
  forall(u v w:R), u ∈ [a,b] /\ v ∈ [a,b] /\w ∈ [a,b] ->
  S u v + S v w = S u w. 

(*中值性*)
Definition median (S:R->R->R)(f:R->R)(a b:R):=
  forall(u v:R), u ∈ [a,b] /\ v ∈ [a,b] /\ v - u > 0 ->
  exists p q:R, p ∈ [u,v] /\ q ∈ [u,v] /\
  f p *(v - u)<=S u v<=f q *(v - u).

(*积分系统*)
Definition integ_sys' (S:R->R->R)(f:R->R)(a b:R) :=
  additivity' S a b /\ median S f a b.

Notation " S ∫ f '(x)dx' " := (integ_sys' S f)(at level 10).

(*可积*)
Definition integrable' f a b :=
  exists S, integ_sys' S f a b /\
  (forall S':R->R->R, integ_sys' S' f a b -> S' = S).

Definition F_f_i (f:R->R)(i n:nat)(x1 x2:R): R :=
  f(x1+(x2-x1)* INR(i+1) / INR(n+1)) - f(x1+(x2-x1)* INR i / INR(n+1)).

Fixpoint sum_f_N (f:R->R)(i n:nat) F (x1 x2:R) : R :=
  match i with
  | 0 => F f 0%nat n x1 x2
  | S p => sum_f_N f p n F x1 x2 + F f i n x1 x2
  end.

Lemma simpl_sum_f_n : forall f u v i n ,
  sum_f_N f i n F_f_i u v = f (u+(v-u)*INR(i+1)/INR(n+1)) - f u.
Proof.
  intros.
  induction i.
  - unfold sum_f_N.  
    unfold F_f_i. simpl.
    rewrite Rmult_0_r. unfold Rdiv. rewrite Rmult_0_l. rewrite Rplus_0_r; auto.
  - assert(sum_f_N f (S i) n F_f_i u v =
           sum_f_N f i n F_f_i u v + F_f_i f (S i) n u v).
     { auto. }
    rewrite H. rewrite IHi.
    unfold F_f_i.
    unfold Rminus. 
    rewrite Rplus_comm. rewrite <- Rplus_assoc.
    apply Rplus_eq_compat_r.
    rewrite <- Nat.add_0_r with (n:= S i).
    rewrite Nat.add_succ_comm. ring.
Qed.

Lemma sum_N : forall f u v n, sum_f_N f n n F_f_i u v = f v - f u.
Proof.
  intros.
  rewrite simpl_sum_f_n.
  unfold Rdiv; rewrite Rinv_r_simpl_l.
  rewrite Rplus_minus; auto.
  apply not_0_INR.
  rewrite Nat.add_comm.
  apply Nat.neq_succ_0.
Qed.

Lemma not_exist' : forall {U: Type} (p: U->Prop), (~ exists x, p x ) ->
 ( forall x,  ~ p x ).
Proof.
  intros.
  unfold not; intro.
  unfold not in H. apply H. 
  exists x; auto.
Qed.


Lemma Rminus_Not_eq0 : forall a b, a<>b -> exists c, c>0 /\ c =Rabs(a - b).
Proof.
  intros.
  generalize (classic (exists c : R, c > 0 /\ c = Rabs (a - b))); intro.
  destruct H0; auto.
  apply not_exist' with(x:=Rabs (a - b)) in H0.
  destruct H0.
  split; auto.
  apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
Qed.

Lemma lemma4_2_1 : forall F f a b, diff_quo_median F f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v - u > 0 ->
  forall i n:nat, (i<=n)%nat ->
  exists x1 x2, x1 ∈ [(u+(v-u)*INR i/INR(n+1)),(u+(v-u)*INR(i+1)/INR(n+1))] /\
                x2 ∈ [(u+(v-u)*INR i/INR(n+1)),(u+(v-u)*INR(i+1)/INR(n+1))] /\
                f x1 <= F_f_i F i n u v /((v-u)/INR(n+1)) <= f x2.
Proof.
  intros.
  unfold diff_quo_median in H.
  destruct H0, H2.
  assert((u+(v-u)*INR i/INR (n+1)) ∈ [a,b]).
   { unfold In; unfold cc.
     unfold In in H0, H2; unfold cc in H0, H2. destruct H0, H2, H4, H5.
     split; auto.
     apply Rplus_le_3_r.
     split.
     - apply Rle_trans with (r2:=a)(r3:=u); auto.
       unfold Rminus; rewrite Rplus_comm.
       apply Rplus_le_reg_r with (r:= -a).
       rewrite Rplus_assoc.
       repeat rewrite Rplus_opp_r.
       rewrite Rplus_0_r.
       apply Rplus_le_reg_r with (r:=(v + - u) * INR i / INR (n+1)).
       rewrite Rplus_opp_l. rewrite Rplus_0_l.
       repeat apply Rmult_le_pos. apply Rlt_le. tauto.
       apply pos_INR. apply Rlt_le. apply Rinv_0_lt_compat.
       apply lt_0_INR. rewrite Nat.add_comm. apply gt_Sn_O.
     - apply Rplus_le_reg_r with (r:= (v - u) * INR i / INR (n+1)).
       rewrite Rminus_plus_r.
       apply Rle_trans with (r2:=v)(r3:=b); auto.
       rewrite <- Rplus_minus with (r1:=u)(r2:=v) at 2.
       apply Rplus_le_compat_l.
       assert (INR i / INR(n+1) < 1).
        { apply Rmult_lt_reg_r with (r:=INR(n+1)).
          apply lt_0_INR. rewrite Nat.add_comm.
          apply gt_Sn_O. unfold Rdiv; rewrite Rinv_mult_rgt0.
          rewrite Rmult_1_l.
          apply lt_INR. rewrite Nat.add_comm. apply le_lt_n_Sm; auto.
          apply lt_0_INR; rewrite Nat.add_comm; apply gt_Sn_O. }
       rewrite <- Rmult_1_r with (r:=v-u) at 2.
       unfold Rdiv. rewrite Rmult_assoc.
       apply Rmult_le_compat_l. apply Rlt_le; auto.
       apply Rlt_le; auto.
   }
   assert((u+(v-u)*INR(i+1)/INR(n+1)) ∈ [a,b]).
   { unfold In; unfold cc.
     unfold In in H0, H2; unfold cc in H0, H2. destruct H0, H2, H4, H5, H6.
     split; auto.
     apply Rplus_le_3_r.
     split.
     - apply Rle_trans with (r2:=a)(r3:=u); auto.
       unfold Rminus; rewrite Rplus_comm.
       apply Rplus_le_reg_r with (r:= -a).
       rewrite Rplus_assoc.
       repeat rewrite Rplus_opp_r.
       rewrite Rplus_0_r.
       apply Rplus_le_reg_r with (r:=(v + - u) * INR (i+1) / INR (n+1)).
       rewrite Rplus_opp_l. rewrite Rplus_0_l.
       repeat apply Rmult_le_pos. apply Rlt_le. tauto.
       apply pos_INR. apply Rlt_le. apply Rinv_0_lt_compat.
       apply lt_0_INR. rewrite Nat.add_comm. apply gt_Sn_O.
     - apply Rplus_le_reg_r with (r:= (v-u)*INR(i+1)/INR(n+1)).
       rewrite Rminus_plus_r.
       apply Rle_trans with (r2:=v)(r3:=b); auto.
       rewrite <- Rplus_minus with (r1:=u)(r2:=v) at 2.
       apply Rplus_le_compat_l.
       assert (INR (i+1) / INR(n+1) <= 1).
        { apply Rmult_le_reg_r with (r:=INR (n+1)).
          apply lt_0_INR. rewrite Nat.add_comm.
          apply gt_Sn_O. unfold Rdiv; rewrite Rinv_mult_rgt0.
          rewrite Rmult_1_l.
          apply le_INR. apply Nat.add_le_mono_r; auto.
          rewrite Nat.add_comm.
          apply lt_0_INR; apply gt_Sn_O. 
        }
       rewrite <- Rmult_1_r with (r:=v-u) at 2.
       unfold Rdiv. rewrite Rmult_assoc.
       apply Rmult_le_compat_l; auto.
       apply Rlt_le; auto.
   }
   assert((u+(v-u)*INR(i+1)/INR(n+1))-(u+(v-u)*INR i/INR(n+1))>0).
   { apply Rgt_minus.
     apply Rplus_gt_compat_l.
     unfold Rdiv; repeat rewrite Rmult_assoc.
     apply Rmult_gt_compat_l; auto.
     apply Rmult_gt_compat_r; auto.
     apply Rinv_0_lt_compat.
     rewrite Nat.add_comm.
     apply lt_0_INR; apply gt_Sn_O.
     apply lt_INR.
     rewrite Nat.add_comm; apply Nat.lt_succ_diag_r. 
   }
   destruct H with (u:=(u + (v - u) * INR i / INR (n + 1)))
                   (v:=(u + (v - u) * INR (i + 1) / INR (n + 1))).
   split; tauto.
   destruct H7, H7, H8.
   exists x, x0.
   split; auto. split; auto.
   unfold F_f_i.
   assert(u+(v-u)*INR(i+1)/INR(n+1)-(u+(v-u)*INR i/INR(n+1)) = (v-u)/INR(n+1)).
    { assert (forall a b c d, a+b-(c+d)=(a-c)+(b-d)). { intros; ring. }
      rewrite H10. 
      assert (forall r, r-r=0). { intro; ring. }
      rewrite H11. rewrite Rplus_0_l.
      unfold Rdiv; repeat rewrite Rmult_assoc.
      rewrite <- Rmult_minus_distr_l with (r1:=v-u).
      unfold Rminus; rewrite Ropp_mult_distr_l.
      rewrite <- Rmult_plus_distr_r.  
      rewrite Nat.add_comm. rewrite S_O_plus_INR.
      rewrite Rplus_assoc; rewrite Rplus_opp_r; rewrite Rplus_0_r.
      rewrite Rmult_1_l; auto. }
    rewrite H10 in H9; auto.
Qed.


Lemma th4_2_1 : forall F f a b,
  diff_quo_median F f a b -> uniform_continuous f a b ->
  forall s:R->R->R, (forall x y, s x y = F y - F x) ->
  integ_sys' s f a b.
Proof.
  intros.
  unfold diff_quo_median in H.
  unfold integ_sys'.
  split.
  - unfold additivity'; intros.
    repeat rewrite H1. ring.
  - unfold median; intros.
    generalize H2; intro.
    apply H in H2; clear H.
    destruct H2, H.
    exists x, x0.
    rewrite H1.
    split. tauto. split. tauto.
    eapply Rinv_le_r with (r:=v-u). tauto.
    unfold Rdiv; repeat rewrite Rinv_r_simpl_l.
    unfold Rdiv in H. tauto.
    apply Rgt_not_eq; tauto.
    apply Rgt_not_eq; tauto.
Qed.

Lemma th4_2_2 : forall F G f a b, diff_quo_median F f a b ->
  diff_quo_median G f a b -> uniform_continuous f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 ->
  G v - G u = F v - F u.
Proof.
  intros.
  generalize ( classic (G v - G u = F v - F u) ); intros.
  destruct H3; auto.
  apply Rminus_Not_eq0 in H3.
  destruct H3, H3; rename x into c.
  unfold uniform_continuous in H1; destruct H1; rename x into d.
  assert(forall n:nat, 0 < (v - u) / INR (n + 1)) as minus_vu.
      { intro.
        unfold Rdiv; apply Rmult_lt_0_compat.
        apply Rgt_lt; tauto.
        apply Rinv_0_lt_compat; apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
  assert(forall n, ((v - u) / INR (n + 1)) ∈ (0,(b - a)]) as In_vu.
      { intro.
        destruct H2, H5.
        unfold In in H2; unfold cc in H2.
        unfold In in H5; unfold cc in H5.
        unfold In; unfold oc.
        destruct H2, H5.
        split. apply Rlt_Rminus; auto.
        split; auto.
        apply Rle_trans with(r2:=v-u).
        rewrite <- Rmult_1_r with (r:=v-u) at 2.
        apply Rmult_le_compat_l; auto.
        apply Rlt_le; apply Rgt_lt; auto.
        rewrite <- Rinv_1. apply Rinv_le_contravar.
        apply Rlt_0_1. 
        generalize (le_INR 1 (n+1)); intro.
        simpl in H9; apply H9.
        rewrite Nat.add_1_r; apply le_n_S; apply Nat.le_0_l.
        unfold Rminus; apply Rplus_le_compat. tauto.
        apply Ropp_le_contravar; tauto. }
  assert(forall n:nat, c<=(v-u)*d((v-u)/ INR (n+1))).
   { intros.
     generalize (lemma4_2_1 F f a b H u v H2); intros.
     generalize (lemma4_2_1 G f a b H0 u v H2); intros.
     generalize (minus_vu n) as minus_vu_n; intro.
     generalize (In_vu n) as In_vu_n; intro.
     assert(forall x, x ∈ [u + (v - u) * INR 0 / INR (n + 1),
                           u + (v - u) * INR (0 + 1) / INR (n + 1)] ->
                      x ∈ [a,b]) as In_x.
      { intros.
        simpl in H7.
        rewrite Rmult_0_r in H7.
        unfold Rdiv in H7; rewrite Rmult_0_l in H7.
        rewrite Rplus_0_r in H7.
        rewrite Rmult_1_r in H7.
        unfold In in H7; unfold cc in H7.
        unfold In; unfold cc.
        destruct H7, H8.
        destruct H2; unfold In in H2; unfold cc in H2.
        destruct H2. split; auto.
        destruct H11. split.
        apply Rle_trans with (r2:=u); auto.
        apply Rle_trans with (r2:=u + (v - u) * / INR (n + 1)); auto.
        destruct H10; unfold In in H10; unfold cc in H10.
        destruct H10, H14.
        apply Rle_trans with (r2:=v); auto.
        rewrite <- Rplus_minus with(r1:=u)(r2:=v) at 2.
        apply Rplus_le_compat_l.
        rewrite <- Rmult_1_r with (r:=v-u) at 2.
        apply Rmult_le_compat_l with (r:=v-u).
        apply Rlt_le; auto.
        rewrite <- Rinv_1. apply Rinv_le_contravar.
        apply Rlt_0_1. 
        generalize (le_INR 1 (n+1)); intro.
        simpl in H16; apply H16.
        rewrite Nat.add_1_r; apply le_n_S; apply Nat.le_0_l. }
     assert(forall x (i:nat), (i<=n)%nat -> x ∈ [u+(v-u)*INR i/INR(n+1),
            u+(v-u)*INR(i+1)/INR(n+1)]->x ∈ [a,b]) as In_xi.
      { intros.
        unfold In in H8; unfold cc in H8.
        unfold In; unfold cc.
        destruct H8, H9.
        destruct H2; unfold In in H2; unfold cc in H2.
        destruct H2. split; auto.
        destruct H12. split.
        apply Rle_trans with (r2:=u); auto.
        apply Rplus_le_reg_pos_r with (r2:=(v-u)*INR i/INR(n+1)); auto.
        repeat apply Rmult_le_pos.
        apply Rge_le; apply Rgt_ge; tauto.
        apply pos_INR.
        apply Rlt_le; apply Rinv_0_lt_compat; apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ.
        apply Rle_trans with (r2:=u+(v-u) * INR(i+1)/INR(n+1)); auto.
        destruct H11; unfold In in H11; unfold cc in H11.
        destruct H11, H15.
        apply Rle_trans with (r2:=v); auto.
        rewrite <- Rplus_minus with(r1:=u)(r2:=v) at 2.
        apply Rplus_le_compat_l.
        rewrite <- Rmult_1_r with (r:=v-u) at 2.
        unfold Rdiv; rewrite Rmult_assoc.
        apply Rmult_le_compat_l with (r:=v-u).
        apply Rlt_le; auto.
        apply Rmult_le_reg_r with(r:=INR (n + 1)).
        apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ.
        rewrite Rmult_1_l.
        rewrite Rinv_mult_rgt0.
        repeat rewrite plus_INR; apply Rplus_le_compat_r.
        apply le_INR; auto.
        apply Rgt_lt; apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
     assert(forall x1 x2, x1 ∈ [u+(v-u)*INR 0/INR(n+1),
       u+(v-u)*INR(0+1)/INR(n+1)] -> x2 ∈ [u+(v-u)*INR 0/INR(n+1),
       u+(v-u)*INR(0+1)/INR(n+1)] -> Rabs(x2-x1)<=(v-u)/INR(n+1)) as In_minus_x.
      { intros.
        simpl in H7, H8.
        rewrite Rmult_0_r in H7, H8.
        unfold Rdiv in H7, H8; rewrite Rmult_0_l in H7, H8.
        rewrite Rplus_0_r in H7, H8.
        rewrite Rmult_1_r in H7, H8.
        unfold In in H7, H8; unfold cc in H7, H8.
        destruct H7, H8.
        apply Rminus_Rabs with(a:=u)(b:=u + (v - u) * / INR (n + 1))
                              (r1:=x1) in H10; auto.
        rewrite <- Rabs_right with(r:=(v - u) / INR (n + 1)).
        rewrite Rplus_comm in H10.
        unfold Rminus in H10.
        rewrite Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
        rewrite Rplus_0_r in H10. destruct H10; unfold Rminus; auto.
        rewrite Ropp_plus_distr in H10.
        rewrite <- Rplus_assoc in H10.
        rewrite Rplus_comm with(r1:=u) in H10; rewrite Rplus_assoc in H10.
        rewrite Rplus_opp_r in H10; rewrite Rplus_0_r in H10.
        rewrite Rabs_Ropp in H10; auto.
        apply Rgt_ge; auto. }
     assert(forall x1 x2 (i:nat), (i<=n)%nat -> x1 ∈ [u+(v-u)*INR i/INR(n+1),
       u+(v-u)*INR(i+1)/INR(n+1)] -> x2 ∈ [u+(v-u)*INR i/INR(n+1),
       u+(v-u)*INR(i+1)/INR(n+1)] ->Rabs(x2-x1)<=(v-u)/INR(n+1)) as In_minus_xi.
      { intros. unfold In in H8, H9; unfold cc in H8, H9.
        destruct H8, H9.
        apply Rminus_Rabs with(a:=u+(v-u)*INR i/INR(n+1))
                              (b:=u+(v-u)*INR(i+1)/INR(n+1))
                              (r1:=x1) in H11; auto.
        rewrite <- Rabs_right with(r:=(v - u) / INR (n + 1)).
        assert(forall a b c, a+b - (a+c) = b-c ). { intros; ring. }
        repeat rewrite H12 in H11. clear H12.
        unfold Rdiv in H11.
        assert(forall a b c d, a*b*c-a*d*c = (b-d)*a*c). { intros; ring. }
        repeat rewrite H12 in H11. clear H12.
        destruct H11.
        rewrite plus_comm in H11; rewrite plus_INR in H11.
        unfold Rminus in H11; rewrite Rplus_assoc in H11.
        rewrite Rplus_opp_r in H11; rewrite Rplus_0_r in H11.
        rewrite Rmult_1_l in H11.
        unfold Rminus; auto.
        unfold Rminus in H11. rewrite plus_INR in H11.
        rewrite Ropp_plus_distr in H11; rewrite <- Rplus_assoc in H11.
        rewrite Rplus_opp_r in H11; rewrite Rplus_0_l in H11.
        rewrite Rmult_assoc in H11.
        rewrite Rabs_mult with (x:=- INR 1 )in H11.
        rewrite Rabs_Ropp in H11. simpl in H11; rewrite Rabs_R1 in H11.
        rewrite Rmult_1_l in H11. unfold Rminus; auto.
        apply Rle_ge; apply Rlt_le; auto. }
     rewrite H4. repeat rewrite <- sum_N with (n:=n).
     assert(forall i:nat, (i<=n)%nat ->
       Rabs (sum_f_N G i n F_f_i u v - sum_f_N F i n F_f_i u v)<=
       ((v - u) / INR (n+1) * INR (i+1)) * d ((v - u) / INR (n+1))).
      { intros.
        induction i. 
        - simpl.
          generalize(H5 0%nat n H7); intros.
          generalize(H6 0%nat n H7); intros.
          destruct H8, H8. destruct H9, H9.
          destruct H8, H10, H9, H12.
          apply Rminus_Rabs with(a:= f x)(b:= f x0)
            (r1:=F_f_i F 0 n u v / ((v - u) / INR (n + 1))) in H13; auto.
          destruct H13.
          generalize (total_eq_or_neq (x2 - x) 0); intro.
          destruct H14.
          + apply Rminus_diag_uniq in H14; rewrite H14 in H13.
            rewrite Rminus_diag_eq with(r1:=f x) in H13; try reflexivity.
            rewrite Rabs_R0 in H13.
            apply Rle_antisym with(r1:=0) in H13; try apply Rabs_pos.
            rewrite <- Rdiv_minus_distr in H13.
            unfold Rdiv in H13; rewrite Rabs_mult in H13.
            apply eq_sym in H13; apply Rmult_integral in H13.
            destruct H13; apply Rlt_le.
            * rewrite H13.
              rewrite Rmult_1_r.
              apply Rmult_lt_0_compat; auto.
              destruct H1, H1.
              apply Rgt_lt; apply H1; auto.
            * apply Rinv_0_lt_compat in minus_vu_n.
              apply Rlt_not_eq in minus_vu_n.
              apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
              apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
              unfold Rdiv in minus_vu_n; rewrite H13 in minus_vu_n.
              contradiction. 
          + assert(Rabs (f x2 - f x) <= d ((v - u) / INR (n + 1))).
             { apply Rle_trans with (r2:=d (Rabs (x2-x))).
               destruct H1, H15.
               rewrite <- Rplus_minus with(r1:=x)(r2:=x2) at 1.
               apply H16 with (x:=x) (h:=x2-x).
               rewrite Rplus_minus.
               split; try apply In_x; auto. 
               apply In_minus_x with(x1:=x) in H12; auto.
               destruct H12.
               destruct H1; unfold pos_inc in H1.
               destruct H1; apply H16; auto.
               * unfold In in In_vu_n; unfold oc in In_vu_n.
                 unfold In; unfold oc.
                 destruct In_vu_n; split; auto.
                 split. apply Rabs_pos_lt; auto.
                 apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                 tauto.
               * rewrite H12. apply Rle_refl. }
             apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H13; auto.
             rewrite Rmult_1_r.
             unfold Rdiv in H13; unfold Rdiv.
             rewrite Rmult_comm with(r1:=F_f_i G 0 n u v)
                                    (r2:=/ ((v - u) * / INR (n + 1))) in H13.
             rewrite Rmult_comm with(r1:=F_f_i F 0 n u v)
                                    (r2:=/ ((v - u) * / INR (n + 1))) in H13.
             rewrite <- Rmult_minus_distr_l in H13.
             rewrite Rabs_mult in H13.
             rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H13.
             apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H13.
             rewrite <- Rmult_assoc in H13.
             rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H13.
             rewrite Rmult_1_l in H13; auto.
             apply Rgt_not_eq; auto.
             apply Rlt_le; auto.
             apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto.
          +  generalize (total_eq_or_neq (x1 - x0) 0); intro.
             destruct H14.
             * apply Rminus_diag_uniq in H14; rewrite H14 in H13.
               rewrite Rminus_diag_eq with(r1:=f x0) in H13; try reflexivity.
               rewrite Rabs_R0 in H13.
               apply Rle_antisym with(r1:=0) in H13; try apply Rabs_pos.
               rewrite <- Rdiv_minus_distr in H13.
               unfold Rdiv in H13; rewrite Rabs_mult in H13.
               apply eq_sym in H13; apply Rmult_integral in H13.
               destruct H13; apply Rlt_le.
               -- rewrite H13.
                 rewrite Rmult_1_r.
                 apply Rmult_lt_0_compat; auto.
                 destruct H1, H1.
                 apply Rgt_lt; apply H1; auto.
               -- apply Rinv_0_lt_compat in minus_vu_n.
                 apply Rlt_not_eq in minus_vu_n.
                 apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
                 apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
                 unfold Rdiv in minus_vu_n; rewrite H13 in minus_vu_n.
                 contradiction. 
             * assert(Rabs (f x1 - f x0) <= d ((v - u) / INR (n + 1))).
                { apply Rle_trans with (r2:=d (Rabs (x1-x0))).
                  destruct H1, H15.
                 rewrite <- Rplus_minus with(r1:=x0)(r2:=x1) at 1.
                 apply H16 with (x:=x0) (h:=x1-x0).
                 rewrite Rplus_minus.
                 split; try apply In_x; auto. 
                 apply In_minus_x with(x1:=x0) in H9; auto.
                 destruct H9.
                 destruct H1; unfold pos_inc in H1.
                 destruct H1; apply H16; auto.
                 - unfold In in In_vu_n; unfold oc in In_vu_n.
                   unfold In; unfold oc.
                   destruct In_vu_n; split; auto.
                   split. apply Rabs_pos_lt; auto.
                   apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                   tauto.
                 - rewrite H9; apply Rle_refl. }
               apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H13; auto.
               rewrite Rmult_1_r.
               unfold Rdiv in H13; unfold Rdiv.
               rewrite Rmult_comm with(r1:=F_f_i G 0 n u v)
                                      (r2:=/ ((v - u) * / INR (n + 1))) in H13.
               rewrite Rmult_comm with(r1:=F_f_i F 0 n u v)
                                      (r2:=/ ((v - u) * / INR (n + 1))) in H13.
               rewrite <- Rmult_minus_distr_l in H13.
               rewrite Rabs_mult in H13.
               rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H13.
               apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H13.
               rewrite <- Rmult_assoc in H13.
               rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H13.
               rewrite Rmult_1_l in H13; auto.
               apply Rgt_not_eq; auto.
               apply Rlt_le; auto.
               apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto.
    - generalize H7; intro.
      apply le_Sn_le in H7. apply IHi in H7. clear IHi.
      assert(sum_f_N G (S i) n F_f_i u v =
        F_f_i G (S i) n u v + sum_f_N G i n F_f_i u v ) as sumG_si_i.
       { unfold F_f_i at 2.
         repeat rewrite simpl_sum_f_n. 
         unfold Rminus. rewrite Rplus_assoc.
         rewrite Nat.add_1_r with(n:=i).
         rewrite <- Rplus_assoc with (r1:=-G(u+(v+-u)*INR(S i)/INR(n+1))).
         rewrite Rplus_opp_l; rewrite Rplus_0_l; auto. }
      assert(sum_f_N F (S i) n F_f_i u v =
        F_f_i F (S i) n u v + sum_f_N F i n F_f_i u v ) as sumF_si_i.
       { unfold F_f_i at 2.
         repeat rewrite simpl_sum_f_n. 
         unfold Rminus. rewrite Rplus_assoc.
         rewrite Nat.add_1_r with(n:=i).
         rewrite <- Rplus_assoc with (r1:=-F(u+(v+-u)*INR(S i)/INR(n+1))).
         rewrite Rplus_opp_l; rewrite Rplus_0_l; auto. }
      rewrite sumG_si_i; rewrite sumF_si_i.
      assert(forall a b c d, a+b-(c+d) = a-c + (b-d)). { intros; ring. }
      rewrite H9. clear H9.
      apply Rle_trans with (r2:=Rabs(F_f_i G (S i) n u v-F_f_i F (S i) n u v)+
        Rabs(sum_f_N G i n F_f_i u v-sum_f_N F i n F_f_i u v)).
      apply Rabs_triang. clear sumG_si_i. clear sumF_si_i.
      assert((v - u) / INR (n + 1) * INR (S i + 1) * d ((v - u) / INR (n + 1))=
             (v - u) / INR (n + 1) * d ((v - u) / INR (n + 1)) +
             (v - u) / INR (n + 1) * INR (i + 1) * d ((v - u) / INR (n + 1))).
       { rewrite plus_INR with(n:=S i). 
         rewrite Rplus_comm with (r1:=INR(S i)).
         rewrite Rmult_comm with(r2:=INR 1 + INR (S i)).
         repeat rewrite Rmult_plus_distr_r.
         rewrite Rmult_1_l.
         rewrite Rmult_comm with (r2:=INR (i + 1)).
         rewrite Nat.add_1_r with(n:=i); auto. }
      rewrite H9; apply Rplus_le_compat; auto. clear H9. clear H7.
      generalize (H5 (S i) n H8); intro.
      generalize (H6 (S i) n H8); intro. clear H5; clear H6.
      destruct H7, H5, H9, H6, H5, H7, H6, H10.
      apply Rminus_Rabs with(a:= f x)(b:= f x0)
            (r1:=F_f_i F (S i) n u v / ((v - u) / INR (n + 1))) in H11; auto.
      destruct H11.
      + generalize (total_eq_or_neq (x2 - x) 0); intro.
        destruct H12.
        * apply Rminus_diag_uniq in H12; rewrite H12 in H11.
          rewrite Rminus_diag_eq with(r1:=f x) in H11; try reflexivity.
          rewrite Rabs_R0 in H11.
          apply Rle_antisym with(r1:=0) in H11; try apply Rabs_pos.
          rewrite <- Rdiv_minus_distr in H11.
          unfold Rdiv in H11; rewrite Rabs_mult in H11.
          apply eq_sym in H11; apply Rmult_integral in H11.
          destruct H11; apply Rlt_le.
          -- rewrite H11.
             apply Rmult_lt_0_compat; auto.
             destruct H1, H1.
             apply Rgt_lt; apply H1; auto.
          -- apply Rinv_0_lt_compat in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n.
             apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
             unfold Rdiv in minus_vu_n; rewrite H11 in minus_vu_n.
             contradiction.
        * assert(Rabs (f x2 - f x) <= d ((v - u) / INR (n + 1))).
             { apply Rle_trans with (r2:=d (Rabs (x2-x))).
               destruct H1, H13.
               rewrite <- Rplus_minus with(r1:=x)(r2:=x2) at 1.
               apply H14 with (x:=x) (h:=x2-x).
               rewrite Rplus_minus.
               split; try apply In_xi with (i:=S i); auto.
               split; try apply In_xi with (i:=S i); auto.
               apply In_minus_xi with(x1:=x)(i:=S i) in H10; auto.
               destruct H10.
               destruct H1; unfold pos_inc in H1.
               destruct H1; apply H14; auto.
               - unfold In in In_vu_n; unfold oc in In_vu_n.
                 unfold In; unfold oc.
                 destruct In_vu_n; split; auto.
                 split. apply Rabs_pos_lt; auto.
                 apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                 tauto.
               - rewrite H10; apply Rle_refl. }
          apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H11; auto.
          unfold Rdiv in H11; unfold Rdiv.
          rewrite Rmult_comm with(r1:=F_f_i G (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite Rmult_comm with(r1:=F_f_i F (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite <- Rmult_minus_distr_l in H11.
          rewrite Rabs_mult in H11.
          rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H11.
          apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite <- Rmult_assoc in H11.
          rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite Rmult_1_l in H11; auto.
          apply Rgt_not_eq; auto.
          apply Rlt_le; auto.
          apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto.
     + generalize (total_eq_or_neq (x1 - x0) 0); intro.
        destruct H12.
        * apply Rminus_diag_uniq in H12; rewrite H12 in H11.
          rewrite Rminus_diag_eq with(r1:=f x0) in H11; try reflexivity.
          rewrite Rabs_R0 in H11.
          apply Rle_antisym with(r1:=0) in H11; try apply Rabs_pos.
          rewrite <- Rdiv_minus_distr in H11.
          unfold Rdiv in H11; rewrite Rabs_mult in H11.
          apply eq_sym in H11; apply Rmult_integral in H11.
          destruct H11; apply Rlt_le.
          -- rewrite H11.
             apply Rmult_lt_0_compat; auto.
             destruct H1, H1.
             apply Rgt_lt; apply H1; auto.
          -- apply Rinv_0_lt_compat in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n.
             apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
             unfold Rdiv in minus_vu_n; rewrite H11 in minus_vu_n.
             contradiction.
        * assert(Rabs (f x1 - f x0) <= d ((v - u) / INR (n + 1))).
             { apply Rle_trans with (r2:=d (Rabs (x1-x0))).
               destruct H1, H13.
               rewrite <- Rplus_minus with(r1:=x0)(r2:=x1) at 1.
               apply H14 with (x:=x0) (h:=x1-x0).
               rewrite Rplus_minus.
               split; try apply In_xi with (i:=S i); auto.
               split; try apply In_xi with (i:=S i); auto.
               apply In_minus_xi with(x1:=x0)(i:=S i) in H6; auto.
               destruct H6.
               destruct H1; unfold pos_inc in H1.
               destruct H1; apply H14; auto.
               - unfold In in In_vu_n; unfold oc in In_vu_n.
                 unfold In; unfold oc.
                 destruct In_vu_n; split; auto.
                 split. apply Rabs_pos_lt; auto.
                 apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                 tauto.
               - rewrite H6; apply Rle_refl. }
          apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H11; auto.
          unfold Rdiv in H11; unfold Rdiv.
          rewrite Rmult_comm with(r1:=F_f_i G (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite Rmult_comm with(r1:=F_f_i F (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite <- Rmult_minus_distr_l in H11.
          rewrite Rabs_mult in H11.
          rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H11.
          apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite <- Rmult_assoc in H11.
          rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite Rmult_1_l in H11; auto.
          apply Rgt_not_eq; auto.
          apply Rlt_le; auto.
          apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto. }
    generalize(Nat.le_refl n); intro.
    apply H7 in H8.
    unfold Rdiv in H8.
    rewrite Rinv_mult_rgt0 in H8; auto.
    apply lt_0_INR.
    rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
  destruct H1, H6.
  unfold pos_inc in H1; unfold bounded_rec_f in H6.
  destruct H1.
  generalize(H6 ((v-u)/c)); intro. destruct H9, H9.
  generalize H9 as In_someone; intro.
  apply H1 in H9.
  unfold Rdiv in H10; rewrite Rmult_1_l in H10.
  rewrite Rabs_Rinv in H10; try apply Rgt_not_eq; auto.
  rewrite Rabs_right in H10; try apply Rgt_ge; auto.
  apply Rmult_lt_compat_r with(r:=c) in H10; auto.
  rewrite Rinv_mult_rgt0 in H10; auto.
  rewrite Rmult_comm in H10.
  apply Rmult_lt_compat_r with(r:=d x) in H10; auto.
  rewrite Rinv_mult_rgt0 in H10; auto.
  assert(exists n:nat, (v - u) / INR (n + 1) < x). 
   { generalize (classic (exists n:nat, (v - u) / INR (n + 1) < x)); intro.
     destruct H11; auto.
     generalize (not_not_archimedean ((v-u)/x-1)); intro.
     destruct H12; intro.
     apply not_exist' with (x:=n)
       (p:= (fun n:nat =>(v - u) / INR (n + 1) < x)) in H11.
     apply not_Rlt in H11.
     unfold In in In_someone; unfold oc in In_someone.
     destruct In_someone, H13.
     apply Rmult_ge_compat_l with (r:=/x) in H11;
     try apply Rgt_ge; try apply Rinv_0_lt_compat; auto.
     rewrite Rinv_l in H11; try apply Rgt_not_eq; auto.
     apply Rmult_ge_compat_r with (r:=INR(n+1)) in H11.
     rewrite Rmult_1_l in H11.
     unfold Rdiv in H11.
     rewrite <- Rmult_assoc in H11. rewrite Rinv_mult_rgt0 in H11.
     rewrite Rmult_comm in H11; rewrite plus_INR in H11.
     apply Rplus_ge_compat_r with(r:=-1) in H11.
     rewrite Rplus_assoc in H11;
     rewrite Rplus_opp_r in H11; rewrite Rplus_0_r in H11.
     apply Rge_le; auto.
     apply lt_0_INR; apply Nat.add_pos_r; apply Nat.lt_0_1.
     apply Rle_ge; apply pos_INR. }
  destruct H11.
  apply H8 in H11; try apply In_vu; auto.
  apply Rmult_le_compat_l with(r:=v-u) in H11.
  generalize (H5 x0); intro.
  apply Rle_trans with(r1:=c) in H11; auto.
  apply Rlt_not_ge in H10.
  apply Rle_ge in H11; contradiction.
  apply Rlt_le; tauto.
Qed.

Theorem Theorem4_2 : forall F f a b,
  diff_quo_median F f a b -> uniform_continuous f a b ->
  integ_sys' (fun u v => F v-F u) f a b /\
  (forall G, diff_quo_median G f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 ->
  G v - G u = F v - F u).
Proof.
  intros.
  split.
  - apply th4_2_1 with (F:=F); auto.
  - intros.
    apply th4_2_2 with (f:=f)(a:=a)(b:=b); auto.
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


Corollary strder_Deduce_der : forall F f a b,
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
      generalize(Rgt_or_ge M 0); intro. destruct H1.
      * assert(exists z : R, z ∈ (0, b - a] /\ z < 1/M).
       { assert(0<b-a).
          { apply Rlt_Rminus; auto. }
         generalize (total_order_T (1/M) (b-a)); intro.
         destruct H3. destruct s.
         - generalize(exist_Rgt_lt 0 (1/M)); intro. destruct H3.
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
      * exists(b-a). repeat split; try apply Rlt_Rminus; auto.
        apply Req_le; auto.
        apply Rgt_ge_trans with(r1:=Rabs (1 / (b - a))) in H1; auto.
        apply Rabs_pos_lt. apply Rgt_not_eq. unfold Rdiv; rewrite Rmult_1_l.
        apply Rinv_0_lt_compat. apply Rlt_Rminus; auto.
    + destruct H0, H0. exists x. split; auto.
      intros.
      rewrite Rmult_assoc; rewrite <- Rabs_mult.
      rewrite (Rabs_pos_eq (h*h)).
      simpl in H2.
      rewrite <- (Rmult_1_r (h * h)); rewrite Rmult_assoc.
      apply H1; tauto.
      apply Rlt_le; apply Rsqr_pos_lt; tauto.
Qed.


Lemma der_moninc : forall F f a b, derivative F f a b -> 
  (forall x, x ∈ [a,b] -> f(x)>0) -> mon_increasing F [a,b].
Proof.
  intros.
  destruct H, H, H1, H2, H2. rename x into d. rename x0 into M.
  unfold mon_increasing.
  intros. generalize(classic(F x <= F y)); intro.
  destruct H5; auto.
  apply Rnot_le_lt in H5. apply Rlt_minus in H5.
  assert(forall n:nat, exists i:nat, (i<=n)%nat /\
    F (x+(y-x)*INR(i+1)/INR(n+1))-F(x+(y-x)*INR i/INR(n+1))<=(F y-F x)/INR(n+1)).
  { intros. generalize(classic(exists i:nat, (i <= n)%nat /\
    F (x+(y-x)*INR(i+1)/INR(n+1))-F(x+(y-x)*INR i/INR(n+1))<=(F y-F x)/INR(n+1))); intro.
    destruct H6; auto.
    generalize(not_exist (fun i=>(i<=n)%nat)(fun i=> F (x+(y-x)*INR(i+1)/INR(n+1))-
    F(x+(y-x)*INR i/INR(n+1))<=(F y-F x)/INR(n+1)) H6); intro. clear H6.
    assert(sum_f_N F n n F_f_i x y>0) as gt_0_sum_F.
     { assert(forall i, (i<=n)%nat -> 
         sum_f_N F i n F_f_i x y > INR (i+1)*(F y-F x)/INR(n+1)).
        { intros i le_i_n. induction i.
          - unfold sum_f_N. unfold F_f_i.
            generalize(H7 0%nat); intro. simpl in H6.
            apply Rnot_le_gt in H6; auto. rewrite Rmult_0_r in H6.
            unfold Rdiv in H6. rewrite Rmult_0_l in H6.
            rewrite Rplus_0_r in H6. rewrite Rmult_1_r in H6.
            simpl. rewrite Rmult_1_r. rewrite Rmult_0_r.
            unfold Rdiv; rewrite Rmult_0_l. 
            rewrite Rplus_0_r. repeat rewrite Rmult_1_l; auto.
          - assert(sum_f_N F (S i) n F_f_i x y =
              sum_f_N F i n F_f_i x y + F_f_i F (S i) n x y). { auto. }
            assert(INR(S i+1)=INR(i+1)+1 ). 
             { rewrite plus_INR. rewrite Nat.add_1_r; auto. }
            unfold Rdiv; rewrite Rmult_assoc.
            rewrite H6. rewrite H8. rewrite Rmult_plus_distr_r.
            rewrite Rmult_1_l. unfold Rdiv in IHi; rewrite <- Rmult_assoc.
            apply Rplus_gt_compat. apply IHi.
            apply le_trans with(m:=S i); auto.
            unfold F_f_i. generalize (H7 (S i)); intros.
            apply Rnot_le_gt in H9; auto. }
       generalize(H6 n); intro.
       unfold Rdiv in H8. rewrite Rinv_r_simpl_m in H8.
       rewrite sum_N in H8. apply Rgt_not_eq in H8. contradiction.
       apply Nat.le_refl. apply Rgt_not_eq; auto.
       apply lt_0_INR. rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
    rewrite <- sum_N with(n:=n) in H5.
    apply Rlt_le in H5.
    apply Rgt_not_le in gt_0_sum_F. contradiction. }
    assert(forall r, exists n, INR n > r).
     { intro. generalize (not_not_archimedean r); intro.
       apply Classical_Pred_Type.not_all_ex_not in H7.
       destruct H7. exists x0. apply Rnot_le_gt; auto. }
    assert(forall n, Rabs(F y-F x)<=M*(y-x)*d((y-x)/INR(n+1))).
     { intros.
       assert(0<INR(n+1)) as lt_0_SN.
        { apply lt_0_INR.
          rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
       destruct H6 with(n:=n). clear H6. destruct H8.
       assert( (x+(y-x)*INR x0/INR(n+1))∈[a, b] /\
         (x+(y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1))∈[a, b] /\
         (y-x)/INR(n+1)<>0 ).
        { generalize H6 as H11.
          clear H5 H6 H7 H8. destruct H4, H4, H6, H5, H5, H9. split.
          - split; auto. split.
            + apply Rle_trans with(r2:=x); auto.
              rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
              rewrite Rplus_assoc; rewrite Rplus_opp_r.
              rewrite Rplus_0_r; apply Rmult_le_pos.
              apply Rmult_le_pos. apply Rlt_le; auto. apply pos_INR.
              apply Rlt_le; apply Rinv_0_lt_compat; auto.
            + apply Rle_trans with(r2:=y); auto.
              rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
              rewrite Rplus_assoc; rewrite Rplus_opp_r.
              rewrite Rplus_0_r. unfold Rminus; unfold Rdiv.
              apply Rmult_le_reg_r with(r:=INR(n+1)); auto.
              rewrite Rinv_mult_rgt0; auto. unfold Rminus in H8.
              apply Rmult_le_compat_l; apply Rlt_le; auto.
              apply lt_INR. rewrite Nat.add_1_r. 
              apply le_lt_n_Sm; auto.
          - split.
            + assert((y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1)=
                (y-x)*INR(x0+1)/INR(n+1)).
               { rewrite plus_INR with(n:=x0). rewrite Rmult_plus_distr_l.
                 unfold Rdiv. rewrite Rmult_plus_distr_r. 
                 rewrite Rmult_1_r; auto. }
              rewrite Rplus_assoc; rewrite H12. clear H12.
              split; auto. split.
              * apply Rle_trans with(r2:=x); auto.
                rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
                rewrite Rplus_assoc; rewrite Rplus_opp_r.
                rewrite Rplus_0_r; apply Rmult_le_pos.
                apply Rmult_le_pos. apply Rlt_le; auto. apply pos_INR.
                apply Rlt_le; apply Rinv_0_lt_compat; auto.
              * apply Rle_trans with(r2:=y); auto.
                rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
                rewrite Rplus_assoc; rewrite Rplus_opp_r.
                rewrite Rplus_0_r. unfold Rminus; unfold Rdiv.
                apply Rmult_le_reg_r with(r:=INR(n+1)); auto.
                rewrite Rinv_mult_rgt0; auto. unfold Rminus in H8.
                apply Rmult_le_compat_l. apply Rlt_le; auto.
                apply le_INR; repeat rewrite Nat.add_1_r.
                apply le_n_S; auto.
            + unfold Rdiv; apply Rgt_not_eq.
              apply Rmult_gt_0_compat; auto.
              apply Rinv_0_lt_compat; auto. }
       generalize H9; intro. apply H3 in H9.
       apply Rle_trans with(r1:=Rabs(F y-F x)/INR(n+1)) in H9.
       unfold Rdiv in H9; rewrite Rabs_mult in H9.
       rewrite Rmult_assoc with(r1:=M) in H9.
       rewrite Rmult_comm with(r1:=(Rabs(y-x)*Rabs(/INR(n+1)))) in H9.
       rewrite <- Rmult_assoc with(r2:=Rabs (y - x)) in H9.
       rewrite Rabs_right with (r:=/ INR (n + 1))in H9.
       rewrite <- Rmult_assoc in H9.
       apply Rmult_le_compat_r with(r:=INR (n + 1)) in H9.
       rewrite Rinv_mult_rgt0 in H9; auto.
       rewrite Rinv_mult_rgt0 in H9; auto.
       rewrite Rabs_right with(r:=y-x) in H9; try apply Rgt_ge; try tauto.
       rewrite Rmult_comm with(r2:=y-x) in H9.
       rewrite <- Rmult_assoc in H9. unfold Rdiv; auto.
       apply Rlt_le; auto. apply Rgt_ge.
       apply Rinv_0_lt_compat; auto.
       generalize(H8); intro.
       apply Rle_trans with(r2:=Rabs(F(x+(y-x)*INR(x0+1)/INR(n+1))-
         F(x+(y-x)*INR x0/INR(n+1)))).
       apply Ropp_le_contravar in H8.
       apply Rsqr_incr_1 in H8. apply Rsqr_le_abs_0 in H8.
       repeat rewrite Rabs_Ropp in H8.
       unfold Rdiv in H8; rewrite Rabs_mult in H8.
       rewrite Rabs_right with(r:=/INR(n+1)) in H8.
       unfold Rdiv; auto. apply Rgt_ge; apply Rinv_0_lt_compat; auto.
       apply Ropp_0_ge_le_contravar; apply Rle_ge.
       apply Rmult_le_reg_r with(r:=INR (n + 1)); auto.
       unfold Rdiv. rewrite Rinv_mult_rgt0; auto.
       rewrite Rmult_0_l; auto. apply Rlt_le; auto.
       apply Ropp_0_ge_le_contravar; apply Rle_ge.
       apply Rle_trans with(r2:=(F y-F x)/INR(n+1)). auto.
       apply Rmult_le_reg_r with(r:=INR (n + 1)); auto.
       unfold Rdiv. rewrite Rinv_mult_rgt0; auto.
       rewrite Rmult_0_l; auto. apply Rlt_le; auto.
       assert(F(x+(y-x)*INR(x0+1)/INR(n+1))=
         F(x+(y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1))).
        { rewrite plus_INR. rewrite Rmult_plus_distr_l.
          unfold Rdiv. rewrite Rmult_plus_distr_r. 
          rewrite Rmult_1_r; rewrite Rplus_assoc; auto. }
       rewrite <- Rabs_Ropp. rewrite <- Rabs_Ropp with
         (x:=(F(x+(y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1))-
          F(x+(y-x)*INR x0/INR(n+1))-f(x+(y-x)*
          INR x0/INR(n+1))*((y-x)/INR(n+1)))).
       apply Rsqr_le_abs_0. apply Rsqr_incr_1.
       apply Ropp_le_contravar.
       apply Rplus_le_reg_l with(r:=-(F(x+(y-x)*INR(x0+1)/INR(n+1))-
         F(x+(y-x)*INR x0/INR(n+1)))). 
       rewrite Rplus_opp_l. rewrite <- H12; auto. 
       assert(-(F(x+(y-x)*INR(x0+1)/INR(n+1))-F(x+(y-x)*INR x0/INR(n+1)))+
               (F(x+(y-x)*INR(x0+1)/INR(n+1))-F(x+(y-x)*INR x0/INR(n+1)) -
               f(x+(y-x)*INR x0/INR(n+1))*((y-x)/INR(n+1)))=
              -f(x+(y-x)*INR x0/INR(n+1))*((y-x)/INR(n+1))). { ring. }
       rewrite H13. clear H13. apply Rlt_le.
       rewrite Ropp_mult_distr_l_reverse.
       apply Ropp_lt_gt_0_contravar; apply Rmult_gt_0_compat.
       apply H0; tauto.
       unfold Rdiv; apply Rmult_gt_0_compat; try tauto.
       apply Rinv_0_lt_compat; auto.
       apply Ropp_0_ge_le_contravar; apply Rle_ge.
       apply Rle_trans with(r2:=(F y-F x)/INR(n+1)); auto.
       unfold Rdiv; apply Rlt_le.
       apply Rmult_lt_reg_r with(r:=INR (n + 1)); auto.
       rewrite Rinv_mult_rgt0; auto. rewrite Rmult_0_l; auto.
       apply Ropp_0_ge_le_contravar; apply Rle_ge.
       apply Rplus_le_reg_r with(r:=f(x+(y-x)*INR x0/INR(n+1))*((y-x)/INR(n+1))).
       rewrite Rminus_plus_r; rewrite Rplus_0_l.
       apply Rle_trans with(r2:=0). rewrite <- H12.
       apply Rle_trans with(r2:=(F y-F x)/INR(n+1)); auto.
       unfold Rdiv; apply Rlt_le.
       apply Rmult_lt_reg_r with(r:=INR (n + 1)); auto.
       rewrite Rinv_mult_rgt0; auto. rewrite Rmult_0_l; auto.
       apply Rlt_le; apply Rmult_gt_0_compat.
       apply H0; tauto.
       unfold Rdiv; apply Rmult_gt_0_compat; try tauto.
       apply Rinv_0_lt_compat; auto. }
   unfold bounded_rec_f in H1.
   generalize(H1 (M*(y-x)/Rabs(F y-F x))); intro.
   destruct H9, H9.
   generalize(H7 ((y-x)/x0 -1)); intro.
   destruct H11. rename x1 into n.
   assert(forall n:nat, 0 < (y - x) / INR (n + 1)) as minus_xy.
    { intro.
      unfold Rdiv; apply Rmult_lt_0_compat.
      apply Rgt_lt; tauto.
      apply Rinv_0_lt_compat; apply lt_0_INR.
      rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
   assert(forall n, ((y-x)/INR(n+1))∈(0,(b-a)]) as In_xy.
    { intro. destruct H4, H12, H4, H12.
      split. apply Rlt_Rminus; auto.
      split; auto.
      apply Rle_trans with(r2:=y-x).
      rewrite <- Rmult_1_r with (r:=y-x) at 2.
      apply Rmult_le_compat_l; auto.
      apply Rlt_le; apply Rgt_lt; auto.
      rewrite <- Rinv_1. apply Rinv_le_contravar.
      apply Rlt_0_1. 
      generalize (le_INR 1 (n0+1)); intro.
      simpl in H16; apply H16.
      rewrite Nat.add_1_r; apply le_n_S; apply Nat.le_0_l.
      unfold Rminus; apply Rplus_le_compat. tauto.
      apply Ropp_le_contravar; tauto. }
   assert(d x0 >0). 
    { unfold pos_inc in H. destruct H.
      apply H; auto. }
   assert(d((y-x)*/INR(n+1))>0).
     { unfold pos_inc in H. destruct H.
      apply H. apply In_xy. }
   assert(M*(y-x)/Rabs(F y-F x)<Rabs(1/d((y-x)/INR(n+1)))).
    { apply Rlt_le_trans with(r2:=Rabs(1/d x0)); auto.
      unfold pos_inc in H. destruct H.
      unfold Rdiv; repeat rewrite Rmult_1_l.
      repeat rewrite Rabs_Rinv; try apply Rgt_not_eq; auto.
      repeat rewrite Rabs_right; try apply Rgt_ge;
      try apply Rgt_not_eq; auto. apply Rinv_le_contravar; auto.
      apply H14; auto. apply In_xy.
      apply Rplus_gt_compat_r with(r:=1) in H11.
      rewrite Rminus_plus_r in H11.
      assert(0<INR (n + 1)).
       { apply lt_0_INR. rewrite Nat.add_1_r. apply Nat.lt_0_succ. }
      apply Rmult_lt_reg_r with (r:=INR (n + 1)); auto.
      rewrite Rinv_mult_rgt0; auto.
      destruct H9, H16.
      apply Rmult_gt_compat_r with(r:=x0) in H11; auto.
      unfold Rdiv in H11. rewrite Rinv_mult_rgt0 in H11; auto.
      rewrite Rmult_comm. rewrite plus_INR. simpl; auto. }
   generalize(H8 n); intro. unfold Rdiv in H14. rewrite Rmult_1_l in H14.
   rewrite Rabs_Rinv in H14; try apply Rgt_not_eq; auto.
   rewrite Rabs_right with(r:=(d((y-x)*/INR(n+1)))) in H14;
   try apply Rgt_ge; auto.
   apply Rmult_lt_compat_l with (r:=d ((y-x)*/INR(n+1))) in H14; auto.
   rewrite Rinv_r in H14; try apply Rgt_not_eq; auto.
   rewrite <- Rmult_assoc in H14.
   assert(0<Rabs (F y - F x)).
    { apply Rabs_pos_lt. apply Rlt_not_eq; auto. }
   apply Rmult_lt_compat_r with (r:=Rabs (F y - F x)) in H14; auto.
   rewrite Rinv_mult_rgt0 in H14; auto. rewrite Rmult_1_l in H14.
   rewrite Rmult_comm in H14. apply Rlt_gt in H14.
   apply Rgt_not_le in H14. contradiction.
Qed.

Lemma der_str_moninc : forall F f a b, derivative F f a b -> 
  (forall x, x ∈ [a,b] -> f(x)>0) -> strict_mon_increasing F [a,b].
Proof.
  intros.
  generalize(der_moninc F f a b H H0).
  intro. unfold mon_increasing in H1.
  unfold strict_mon_increasing; intros.
  generalize H2 as In_xy; intro.
  apply H1 in H2. destruct H2; auto.
  destruct H, H, H3, H4, H4. rename x0 into d.
  rename x1 into M. unfold bounded_rec_f in H3.
  generalize(H3 (M/Rabs(f x))); intro.
  destruct H6, H6.
  assert(exists r, 0<r<x0/\0<r<y-x).
   { generalize (total_order_T (y-x) x0); intro.
     assert(forall r, 0<r -> 0<r/2). 
      { intros. apply Rmult_lt_reg_r with(r:=2). apply Rlt_0_2.
        rewrite Rmult_0_l. 
        unfold Rdiv; rewrite Rinv_mult_rgt0; try tauto.
        apply Rlt_0_2. }
     assert(forall r, 0<r -> r/2<r). 
      { intros. apply Rmult_lt_reg_r with(r:=2). apply Rlt_0_2. 
        unfold Rdiv; rewrite Rinv_mult_rgt0; try tauto.
        rewrite Rmult_comm; rewrite double.
        apply Rminus_gt. unfold Rminus.
        rewrite Rplus_assoc. rewrite Rplus_opp_r.
        rewrite Rplus_0_r; auto. apply Rlt_0_2. }
     destruct H8. destruct s.
     exists ((y-x)/2). repeat split; try apply H9; try tauto.
     apply Rlt_trans with(r2:=(y-x)); auto.
     apply H10; tauto. apply H10; tauto.
     exists ((y-x)/2).  rewrite <- e.
     repeat split; try apply H9; try tauto.
     apply H10; tauto. apply H10; tauto.
     exists (x0/2). destruct H6, H8. repeat split; try apply H9; auto.
     apply Rlt_trans with(r2:=x0); auto. }
  destruct H8. rename x1 into h.
  generalize(H5 x h); intro.
  generalize(H1 x (x+h)); intro.
  generalize(H1 (x+h) y); intro.
  assert(x ∈ [a, b] /\ (x + h) ∈ [a, b] /\ h <> 0). 
   { clear H6 H7 H9 H10 H11.
     split; try tauto. destruct In_xy, H6, H9, H7, H7, H12, H8, H14.
     repeat split; auto.
     apply Rle_trans with(r2:=x); auto.
     rewrite <- Rplus_0_r with(r:=x) at 1.
     apply Rplus_le_compat. apply Req_le; auto.
     apply Rlt_le; auto.
     apply Rle_trans with(r2:=y); auto.
     apply Rplus_lt_compat_r with(r:=x) in H15.
     rewrite Rminus_plus_r in H15; rewrite Rplus_comm in H15.
     apply Rlt_le; auto.
     apply Rgt_not_eq; auto. }
  assert(F (x + h) - F x = 0).
   { assert(F x <= F (x+h)).
      { destruct H12, H13.
        apply H1. split; auto. split; auto.
        assert(x+h-x=h). { ring. }
        rewrite H15. destruct H8, H8; auto. }
     assert(F (x+h) <= F y).
      { destruct H12, H14. apply H1. split; auto.
        split; try tauto. destruct H8, H16. apply Rgt_minus.
        apply Rplus_lt_compat_r with(r:=x) in H17.
        rewrite Rminus_plus_r in H17; rewrite Rplus_comm in H17; auto. }
     rewrite <- H2 in H14; apply Rminus_diag_eq.
     apply Rle_antisym; auto. }
  assert(h ∈ (0, b - a]) as In_h.
   { destruct H6, H14.
     split; auto. destruct H8, H8.
     split; auto. apply Rlt_le; auto.
     apply Rlt_le_trans with(r2:=x0); auto. }
  assert(0 < d h) as lt_0_dh.
   { unfold pos_inc in H. destruct H.
     apply H; auto. }
  assert(0 < d x0) as lt_0_dx0.
   { unfold pos_inc in H. destruct H.
     apply H; auto. }
  apply H9 in H12. rewrite H13 in H12.
  rewrite Rminus_0_l in H12. rewrite Rabs_Ropp in H12.
  rewrite Rabs_mult in H12. rewrite Rmult_assoc in H12.
  rewrite Rmult_comm with(r1:=Rabs h)(r2:=d (Rabs h)) in H12.
  rewrite <- Rmult_assoc in H12.
  apply Rmult_le_reg_r with(r:=Rabs h) in H12.
  unfold Rdiv in H7. rewrite Rmult_1_l in H7.
  rewrite Rabs_Rinv in H7.
  apply Rmult_lt_compat_l with(r:=Rabs (d x0)) in H7.
  rewrite Rinv_r in H7. rewrite <- Rmult_assoc in H7.
  apply Rmult_lt_compat_r with(r:=Rabs (f x)) in H7.
  rewrite Rmult_1_l in H7.  rewrite Rmult_assoc in H7.
  rewrite Rmult_comm with(r1:=/ Rabs (f x)) in H7;
  rewrite Rinv_r in H7. rewrite Rmult_1_r in H7.
  apply Rle_lt_trans with(r1:=Rabs (d h) * M) in H7.
  rewrite Rabs_right with (r:=d h) in H7.
  rewrite Rabs_right with (r:=h)in H12.
  rewrite Rmult_comm in H7.
  apply Rlt_not_le in H7. contradiction.
  destruct H8, H8. apply Rgt_ge; auto.
  apply Rgt_ge; auto.  
  apply Rmult_le_compat_r with(r:=M). apply Rlt_le; auto.  
  repeat rewrite Rabs_right. destruct H. apply H14; auto.
  destruct H8, H8; auto.
  apply Rgt_ge; auto. apply Rgt_ge; auto.
  apply Rgt_not_eq; apply Rabs_pos_lt;
  apply Rgt_not_eq; apply H0; tauto.
  apply Rabs_pos_lt;
  apply Rgt_not_eq; apply H0; tauto.
  apply Rgt_not_eq; apply Rabs_pos_lt;
  apply Rgt_not_eq; auto.
  apply Rabs_pos_lt;
  apply Rgt_not_eq; auto.
  apply Rgt_not_eq; auto.
  destruct H8, H8.
  apply Rabs_pos_lt; apply Rgt_not_eq; auto.
Qed.


Lemma der_mondec : forall F f a b, derivative F f a b -> 
  (forall x, x ∈ [a,b] -> f(x)<0) -> mon_decreasing F [a,b].
Proof.
  intros.
  destruct H, H, H1, H2, H2. rename x into d. rename x0 into M.
  unfold mon_decreasing.
  intros. generalize(classic(F x >= F y)); intro.
  destruct H5; auto.
  apply Rnot_ge_gt in H5. apply Rgt_minus in H5.
  assert(forall n:nat, exists i:nat, (i<=n)%nat /\
    F (x+(y-x)*INR(i+1)/INR(n+1))-F(x+(y-x)*INR i/INR(n+1))>=(F y-F x)/INR(n+1)).
  { intros. generalize(classic(exists i:nat, (i <= n)%nat /\
    F (x+(y-x)*INR(i+1)/INR(n+1))-F(x+(y-x)*INR i/INR(n+1))>=(F y-F x)/INR(n+1))); intro.
    destruct H6; auto.
    generalize(not_exist (fun i=>(i<=n)%nat)(fun i=> F (x+(y-x)*INR(i+1)/INR(n+1))-
    F(x+(y-x)*INR i/INR(n+1))>=(F y-F x)/INR(n+1)) H6); intro. clear H6.
    assert(sum_f_N F n n F_f_i x y<0) as gt_0_sum_F.
     { assert(forall i, (i<=n)%nat -> 
         sum_f_N F i n F_f_i x y < INR (i+1)*(F y-F x)/INR(n+1)).
        { intros i le_i_n. induction i.
          - unfold sum_f_N. unfold F_f_i.
            generalize(H7 0%nat); intro. simpl in H6.
            apply Rnot_ge_lt in H6; auto. rewrite Rmult_0_r in H6.
            unfold Rdiv in H6. rewrite Rmult_0_l in H6.
            rewrite Rplus_0_r in H6. rewrite Rmult_1_r in H6.
            simpl. rewrite Rmult_1_r. rewrite Rmult_0_r.
            unfold Rdiv; rewrite Rmult_0_l. 
            rewrite Rplus_0_r. repeat rewrite Rmult_1_l; auto.
          - assert(sum_f_N F (S i) n F_f_i x y =
              sum_f_N F i n F_f_i x y + F_f_i F (S i) n x y). { auto. }
            assert(INR(S i+1)=INR(i+1)+1 ). 
             { rewrite plus_INR. rewrite Nat.add_1_r; auto. }
            unfold Rdiv; rewrite Rmult_assoc.
            rewrite H6. rewrite H8. rewrite Rmult_plus_distr_r.
            rewrite Rmult_1_l. unfold Rdiv in IHi; rewrite <- Rmult_assoc.
            apply Rplus_gt_compat. apply IHi.
            apply le_trans with(m:=S i); auto.
            unfold F_f_i. generalize (H7 (S i)); intros.
            apply Rnot_ge_lt in H9; auto. }
       generalize(H6 n); intro.
       unfold Rdiv in H8. rewrite Rinv_r_simpl_m in H8.
       rewrite sum_N in H8. apply Rgt_not_eq in H8. contradiction.
       apply Nat.le_refl. apply Rgt_not_eq; auto.
       apply lt_0_INR. rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
    rewrite <- sum_N with(n:=n) in H5.
    apply Rlt_le in H5.
    apply Rgt_not_le in gt_0_sum_F. contradiction. }
    assert(forall r, exists n, INR n > r).
     { intro. generalize (not_not_archimedean r); intro.
       apply Classical_Pred_Type.not_all_ex_not in H7.
       destruct H7. exists x0. apply Rnot_le_gt; auto. }
    assert(forall n, Rabs(F y-F x)<=M*(y-x)*d((y-x)/INR(n+1))).
     { intros.
       assert(0<INR(n+1)) as lt_0_SN.
        { apply lt_0_INR.
          rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
       destruct H6 with(n:=n). clear H6. destruct H8.
       assert( (x+(y-x)*INR x0/INR(n+1))∈[a, b] /\
         (x+(y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1))∈[a, b] /\
         (y-x)/INR(n+1)<>0 ).
        { generalize H6 as H11.
          clear H5 H6 H7 H8. destruct H4, H4, H6, H5, H5, H9. split.
          - split; auto. split.
            + apply Rle_trans with(r2:=x); auto.
              rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
              rewrite Rplus_assoc; rewrite Rplus_opp_r.
              rewrite Rplus_0_r; apply Rmult_le_pos.
              apply Rmult_le_pos. apply Rlt_le; auto. apply pos_INR.
              apply Rlt_le; apply Rinv_0_lt_compat; auto.
            + apply Rle_trans with(r2:=y); auto.
              rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
              rewrite Rplus_assoc; rewrite Rplus_opp_r.
              rewrite Rplus_0_r. unfold Rminus; unfold Rdiv.
              apply Rmult_le_reg_r with(r:=INR(n+1)); auto.
              rewrite Rinv_mult_rgt0; auto. unfold Rminus in H8.
              apply Rmult_le_compat_l; apply Rlt_le; auto.
              apply lt_INR. rewrite Nat.add_1_r. 
              apply le_lt_n_Sm; auto.
          - split.
            + assert((y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1)=
                (y-x)*INR(x0+1)/INR(n+1)).
               { rewrite plus_INR with(n:=x0). rewrite Rmult_plus_distr_l.
                 unfold Rdiv. rewrite Rmult_plus_distr_r. 
                 rewrite Rmult_1_r; auto. }
              rewrite Rplus_assoc; rewrite H12. clear H12.
              split; auto. split.
              * apply Rle_trans with(r2:=x); auto.
                rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
                rewrite Rplus_assoc; rewrite Rplus_opp_r.
                rewrite Rplus_0_r; apply Rmult_le_pos.
                apply Rmult_le_pos. apply Rlt_le; auto. apply pos_INR.
                apply Rlt_le; apply Rinv_0_lt_compat; auto.
              * apply Rle_trans with(r2:=y); auto.
                rewrite Rplus_comm; apply Rplus_le_reg_r with(r:=-x).
                rewrite Rplus_assoc; rewrite Rplus_opp_r.
                rewrite Rplus_0_r. unfold Rminus; unfold Rdiv.
                apply Rmult_le_reg_r with(r:=INR(n+1)); auto.
                rewrite Rinv_mult_rgt0; auto. unfold Rminus in H8.
                apply Rmult_le_compat_l. apply Rlt_le; auto.
                apply le_INR; repeat rewrite Nat.add_1_r.
                apply le_n_S; auto.
            + unfold Rdiv; apply Rgt_not_eq.
              apply Rmult_gt_0_compat; auto.
              apply Rinv_0_lt_compat; auto. }
       generalize H9; intro. apply H3 in H9.
       apply Rle_trans with(r1:=Rabs(F y-F x)/INR(n+1)) in H9.
       unfold Rdiv in H9; rewrite Rabs_mult in H9.
       rewrite Rmult_assoc with(r1:=M) in H9.
       rewrite Rmult_comm with(r1:=(Rabs(y-x)*Rabs(/INR(n+1)))) in H9.
       rewrite <- Rmult_assoc with(r2:=Rabs (y - x)) in H9.
       rewrite Rabs_right with (r:=/ INR (n + 1))in H9.
       rewrite <- Rmult_assoc in H9.
       apply Rmult_le_compat_r with(r:=INR (n + 1)) in H9.
       rewrite Rinv_mult_rgt0 in H9; auto.
       rewrite Rinv_mult_rgt0 in H9; auto.
       rewrite Rabs_right with(r:=y-x) in H9; try apply Rgt_ge; try tauto.
       rewrite Rmult_comm with(r2:=y-x) in H9.
       rewrite <- Rmult_assoc in H9. unfold Rdiv; auto.
       apply Rlt_le; auto. apply Rgt_ge.
       apply Rinv_0_lt_compat; auto.
       generalize(H8); intro.
       apply Rle_trans with(r2:=Rabs(F(x+(y-x)*INR(x0+1)/INR(n+1))-
         F(x+(y-x)*INR x0/INR(n+1)))).
       apply Rge_le in H8.   
       apply Rsqr_incr_1 in H8. apply Rsqr_le_abs_0 in H8.
       repeat rewrite Rabs_Ropp in H8.
       unfold Rdiv in H8; rewrite Rabs_mult in H8.
       rewrite Rabs_right with(r:=/INR(n+1)) in H8.
       unfold Rdiv; auto. apply Rgt_ge; apply Rinv_0_lt_compat; auto.
       apply Rmult_le_reg_r with(r:=INR (n + 1)); auto.
       unfold Rdiv. rewrite Rinv_mult_rgt0; auto.
       rewrite Rmult_0_l; auto. apply Rlt_le; auto.
       apply Rle_trans with(r2:=(F y-F x)/INR(n+1)); auto.
       apply Rmult_le_reg_r with(r:=INR (n + 1)); auto.
       unfold Rdiv. rewrite Rinv_mult_rgt0; auto.
       rewrite Rmult_0_l; auto. apply Rlt_le; auto.
       assert(F(x+(y-x)*INR(x0+1)/INR(n+1))=
         F(x+(y-x)*INR x0/INR(n+1)+(y-x)/INR(n+1))).
        { rewrite plus_INR. rewrite Rmult_plus_distr_l.
          unfold Rdiv. rewrite Rmult_plus_distr_r. 
          rewrite Rmult_1_r; rewrite Rplus_assoc; auto. }
       apply Rsqr_le_abs_0. apply Rsqr_incr_1.
       apply Rplus_le_reg_l with(r:=-(F(x+(y-x)*INR(x0+1)/INR(n+1))-
         F(x+(y-x)*INR x0/INR(n+1)))). 
       rewrite Rplus_opp_l. rewrite <- H12; auto. 
       assert(-(F(x+(y-x)*INR(x0+1)/INR(n+1))-F(x+(y-x)*INR x0/INR(n+1)))+
               (F(x+(y-x)*INR(x0+1)/INR(n+1))-F(x+(y-x)*INR x0/INR(n+1)) -
               f(x+(y-x)*INR x0/INR(n+1))*((y-x)/INR(n+1)))=
              -f(x+(y-x)*INR x0/INR(n+1))*((y-x)/INR(n+1))). { ring. }
       rewrite H13. clear H13. apply Rlt_le.
       rewrite Ropp_mult_distr_l_reverse.
       apply Ropp_gt_lt_0_contravar.
       apply Rmult_lt_reg_r with (r:=/((y-x)/INR(n+1))).
       unfold Rdiv; apply Rinv_0_lt_compat;
       apply Rmult_gt_0_compat; try tauto.
       apply Rinv_0_lt_compat; auto. rewrite Rmult_0_l.
       rewrite Rinv_r_simpl_l. apply H0; tauto.
       apply Rgt_not_eq; unfold Rdiv; apply Rmult_gt_0_compat; try tauto.
       apply Rinv_0_lt_compat; auto.
       apply Rge_le in H11.
       apply Rle_trans with(r2:=(F y-F x)/INR(n+1)); auto.
       unfold Rdiv; apply Rlt_le.
       apply Rmult_lt_reg_r with(r:=INR (n + 1)); auto.
       rewrite Rinv_mult_rgt0; auto. rewrite Rmult_0_l; auto.
       apply Rplus_le_reg_r with(r:=f(x+(y-x)*INR x0/INR(n+1))*((y-x)/INR(n+1))).
       rewrite Rminus_plus_r; rewrite Rplus_0_l.
       apply Rle_trans with(r2:=0). apply Rlt_le.
       apply Rmult_lt_reg_r with (r:=/((y-x)/INR(n+1))).
       unfold Rdiv; apply Rinv_0_lt_compat;
       apply Rmult_gt_0_compat; try tauto.
       apply Rinv_0_lt_compat; auto. rewrite Rmult_0_l.
       rewrite Rinv_r_simpl_l. apply H0; tauto.
       unfold Rdiv; apply Rgt_not_eq.
       unfold Rdiv; apply Rmult_gt_0_compat; try tauto.
       apply Rinv_0_lt_compat; auto. 
       rewrite <- H12; apply Rge_le in H11.
       apply Rle_trans with(r2:=(F y-F x)/INR(n+1)); auto.
       unfold Rdiv; apply Rlt_le.
       apply Rmult_lt_reg_r with(r:=INR (n + 1)); auto.
       rewrite Rinv_mult_rgt0; auto. rewrite Rmult_0_l; auto. }
   unfold bounded_rec_f in H1.
   generalize(H1 (M*(y-x)/Rabs(F y-F x))); intro.
   destruct H9, H9.
   generalize(H7 ((y-x)/x0 -1)); intro.
   destruct H11. rename x1 into n.
   assert(forall n:nat, 0 < (y - x) / INR (n + 1)) as minus_xy.
    { intro.
      unfold Rdiv; apply Rmult_lt_0_compat.
      apply Rgt_lt; tauto.
      apply Rinv_0_lt_compat; apply lt_0_INR.
      rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
   assert(forall n, ((y-x)/INR(n+1))∈(0,(b-a)]) as In_xy.
    { intro. destruct H4, H12, H4, H12.
      split. apply Rlt_Rminus; auto.
      split; auto.
      apply Rle_trans with(r2:=y-x).
      rewrite <- Rmult_1_r with (r:=y-x) at 2.
      apply Rmult_le_compat_l; auto.
      apply Rlt_le; apply Rgt_lt; auto.
      rewrite <- Rinv_1. apply Rinv_le_contravar.
      apply Rlt_0_1. 
      generalize (le_INR 1 (n0+1)); intro.
      simpl in H16; apply H16.
      rewrite Nat.add_1_r; apply le_n_S; apply Nat.le_0_l.
      unfold Rminus; apply Rplus_le_compat. tauto.
      apply Ropp_le_contravar; tauto. }
   assert(d x0 >0). 
    { unfold pos_inc in H. destruct H.
      apply H; auto. }
   assert(d((y-x)*/INR(n+1))>0).
     { unfold pos_inc in H. destruct H.
      apply H. apply In_xy. }
   assert(M*(y-x)/Rabs(F y-F x)<Rabs(1/d((y-x)/INR(n+1)))).
    { apply Rlt_le_trans with(r2:=Rabs(1/d x0)); auto.
      unfold pos_inc in H. destruct H.
      unfold Rdiv; repeat rewrite Rmult_1_l.
      repeat rewrite Rabs_Rinv; try apply Rgt_not_eq; auto.
      repeat rewrite Rabs_right; try apply Rgt_ge;
      try apply Rgt_not_eq; auto. apply Rinv_le_contravar; auto.
      apply H14; auto. apply In_xy.
      apply Rplus_gt_compat_r with(r:=1) in H11.
      rewrite Rminus_plus_r in H11.
      assert(0<INR (n + 1)).
       { apply lt_0_INR. rewrite Nat.add_1_r. apply Nat.lt_0_succ. }
      apply Rmult_lt_reg_r with (r:=INR (n + 1)); auto.
      rewrite Rinv_mult_rgt0; auto.
      destruct H9, H16.
      apply Rmult_gt_compat_r with(r:=x0) in H11; auto.
      unfold Rdiv in H11. rewrite Rinv_mult_rgt0 in H11; auto.
      rewrite Rmult_comm. rewrite plus_INR. simpl; auto. }
   generalize(H8 n); intro. unfold Rdiv in H14. rewrite Rmult_1_l in H14.
   rewrite Rabs_Rinv in H14; try apply Rgt_not_eq; auto.
   rewrite Rabs_right with(r:=(d((y-x)*/INR(n+1)))) in H14;
   try apply Rgt_ge; auto.
   apply Rmult_lt_compat_l with (r:=d ((y-x)*/INR(n+1))) in H14; auto.
   rewrite Rinv_r in H14; try apply Rgt_not_eq; auto.
   rewrite <- Rmult_assoc in H14.
   assert(0<Rabs (F y - F x)).
    { apply Rabs_pos_lt. apply Rgt_not_eq; auto. }
   apply Rmult_lt_compat_r with (r:=Rabs (F y - F x)) in H14; auto.
   rewrite Rinv_mult_rgt0 in H14; auto. rewrite Rmult_1_l in H14.
   rewrite Rmult_comm in H14. apply Rlt_gt in H14.
   apply Rgt_not_le in H14. contradiction.
Qed.

Lemma der_str_mondec : forall F f a b, derivative F f a b -> 
  (forall x, x ∈ [a,b] -> f(x)<0) -> strict_mon_decreasing F [a,b].
Proof.
  intros.
  generalize(der_mondec F f a b H H0).
  intro. unfold mon_decreasing in H1.
  unfold strict_mon_decreasing; intros.
  generalize H2 as In_xy; intro.
  apply H1 in H2. destruct H2; auto.
  destruct H, H, H3, H4, H4. rename x0 into d.
  rename x1 into M. unfold bounded_rec_f in H3.
  generalize(H3 (M/Rabs(f x))); intro.
  destruct H6, H6.
  assert(exists r, 0<r<x0/\0<r<y-x).
   { generalize (total_order_T (y-x) x0); intro.
     assert(forall r, 0<r -> 0<r/2). 
      { intros. apply Rmult_lt_reg_r with(r:=2). apply Rlt_0_2.
        rewrite Rmult_0_l. 
        unfold Rdiv; rewrite Rinv_mult_rgt0; try tauto.
        apply Rlt_0_2. }
     assert(forall r, 0<r -> r/2<r). 
      { intros. apply Rmult_lt_reg_r with(r:=2). apply Rlt_0_2. 
        unfold Rdiv; rewrite Rinv_mult_rgt0; try tauto.
        rewrite Rmult_comm; rewrite double.
        apply Rminus_gt. unfold Rminus.
        rewrite Rplus_assoc. rewrite Rplus_opp_r.
        rewrite Rplus_0_r; auto. apply Rlt_0_2. }
     destruct H8. destruct s.
     exists ((y-x)/2). repeat split; try apply H9; try tauto.
     apply Rlt_trans with(r2:=(y-x)); auto.
     apply H10; tauto. apply H10; tauto.
     exists ((y-x)/2).  rewrite <- e.
     repeat split; try apply H9; try tauto.
     apply H10; tauto. apply H10; tauto.
     exists (x0/2). destruct H6, H8. repeat split; try apply H9; auto.
     apply Rlt_trans with(r2:=x0); auto. }
  destruct H8. rename x1 into h.
  generalize(H5 x h); intro.
  generalize(H1 x (x+h)); intro.
  generalize(H1 (x+h) y); intro.
  assert(x ∈ [a, b] /\ (x + h) ∈ [a, b] /\ h <> 0). 
   { clear H6 H7 H9 H10 H11.
     split; try tauto. destruct In_xy, H6, H9, H7, H7, H12, H8, H14.
     repeat split; auto.
     apply Rle_trans with(r2:=x); auto.
     rewrite <- Rplus_0_r with(r:=x) at 1.
     apply Rplus_le_compat. apply Req_le; auto.
     apply Rlt_le; auto.
     apply Rle_trans with(r2:=y); auto.
     apply Rplus_lt_compat_r with(r:=x) in H15.
     rewrite Rminus_plus_r in H15; rewrite Rplus_comm in H15.
     apply Rlt_le; auto.
     apply Rgt_not_eq; auto. }
  assert(F (x + h) - F x = 0).
   { assert(F x >= F (x+h)).
      { destruct H12, H13.
        apply H1. split; auto. split; auto.
        assert(x+h-x=h). { ring. }
        rewrite H15. destruct H8, H8; auto. }
     assert(F (x+h) >= F y).
      { destruct H12, H14. apply H1. split; auto.
        split; try tauto. destruct H8, H16. apply Rgt_minus.
        apply Rplus_lt_compat_r with(r:=x) in H17.
        rewrite Rminus_plus_r in H17; rewrite Rplus_comm in H17; auto. }
     rewrite <- H2 in H14; apply Rminus_diag_eq.
     apply Rge_antisym; auto. }
  assert(h ∈ (0, b - a]) as In_h.
   { destruct H6, H14.
     split; auto. destruct H8, H8.
     split; auto. apply Rlt_le; auto.
     apply Rlt_le_trans with(r2:=x0); auto. }
  assert(0 < d h) as lt_0_dh.
   { unfold pos_inc in H. destruct H.
     apply H; auto. }
  assert(0 < d x0) as lt_0_dx0.
   { unfold pos_inc in H. destruct H.
     apply H; auto. }
  apply H9 in H12. rewrite H13 in H12.
  rewrite Rminus_0_l in H12. rewrite Rabs_Ropp in H12.
  rewrite Rabs_mult in H12. rewrite Rmult_assoc in H12.
  rewrite Rmult_comm with(r1:=Rabs h)(r2:=d (Rabs h)) in H12.
  rewrite <- Rmult_assoc in H12.
  apply Rmult_le_reg_r with(r:=Rabs h) in H12.
  unfold Rdiv in H7. rewrite Rmult_1_l in H7.
  rewrite Rabs_Rinv in H7.
  apply Rmult_lt_compat_l with(r:=Rabs (d x0)) in H7.
  rewrite Rinv_r in H7. rewrite <- Rmult_assoc in H7.
  apply Rmult_lt_compat_r with(r:=Rabs (f x)) in H7.
  rewrite Rmult_1_l in H7.  rewrite Rmult_assoc in H7.
  rewrite Rmult_comm with(r1:=/ Rabs (f x)) in H7;
  rewrite Rinv_r in H7. rewrite Rmult_1_r in H7.
  apply Rle_lt_trans with(r1:=Rabs (d h) * M) in H7.
  rewrite Rabs_right with (r:=d h) in H7.
  rewrite Rabs_right with (r:=h)in H12.
  rewrite Rmult_comm in H7.
  apply Rlt_not_le in H7. contradiction.
  destruct H8, H8. apply Rgt_ge; auto.
  apply Rgt_ge; auto.  
  apply Rmult_le_compat_r with(r:=M). apply Rlt_le; auto.  
  repeat rewrite Rabs_right. destruct H. apply H14; auto.
  destruct H8, H8; auto.
  apply Rgt_ge; auto. apply Rgt_ge; auto.
  apply Rgt_not_eq; apply Rabs_pos_lt;
  apply Rlt_not_eq; apply H0; tauto.
  apply Rabs_pos_lt;
  apply Rlt_not_eq; apply H0; tauto.
  apply Rgt_not_eq; apply Rabs_pos_lt;
  apply Rgt_not_eq; auto.
  apply Rabs_pos_lt;
  apply Rgt_not_eq; auto.
  apply Rgt_not_eq; auto.
  destruct H8, H8.
  apply Rabs_pos_lt; apply Rgt_not_eq; auto.
Qed.


(* 若 F 和 G 都在[ a , b] 上一致可导 ,
f (x)和 g(x)分别是 F(x)和 G(x)的导数.如果
F(b)-F(a)=G(b)-G(a), 则在[ a , b] 上有两点
u 、v ,使得 f (u)≥g(u), f(v)≤g(v) *)
Lemma Valuation_der : forall F G f g a b, a < b ->derivative F f a b ->
  derivative G g a b -> F b - F a = G b - G a ->
  exists u v, u ∈ [a, b] /\ v ∈ [a, b] /\ f u <= g u /\ f v >= g v.
Proof.
  intros F G f g a b lt_a_b. intros.
  assert(derivative (plus_Fu F (mult_real_f (-1) G))
        (plus_Fu f (mult_real_f (-1) g)) a b) as pm.
   { generalize (Theorem3_1_1 a b (-1) G g H0); intro.
     apply Theorem3_1_2 with(F:=F)(f:=f) in H2; auto. }
  assert(a ∈ [a, b] /\ b ∈ [a, b] /\ b - a > 0) as Domain_a_b.
   { repeat split; auto. apply Rle_refl.
     apply Rlt_le; auto. apply Rlt_le; auto.
     apply Rle_refl. apply Rgt_minus. apply Rgt_lt; auto. }
  assert((exists u, u ∈ [a, b] /\ f u <= g u) /\
    (exists v, v ∈ [a, b] /\ f v >= g v) ->
    (exists u v, u ∈ [a, b] /\ v ∈ [a, b] /\ f u <= g u /\ f v >= g v)).
   { intro. destruct H2, H2, H2, H3, H3.
     exists x, x0; split; auto. }
  assert(forall r, -1*r=-r) as Rmult_opp_1_l. { intro; ring. }
  apply H2. clear H2. split.
  - generalize(classic(exists u : R, u ∈ [a, b] /\ f u <= g u)); intro.
    destruct H2; auto.
    assert(~ (exists u, u ∈ [a, b] /\ f u <= g u) ->
     forall u, u ∈ [a, b] -> ~(f u <= g u)).
    { intros. unfold not; intro. destruct H3.
      exists u; split; auto. }
    generalize(H3 H2); intro. clear H3.
    assert(forall x, x ∈ [a, b] -> f x - g x > 0).
     { intros. apply H4 in H3. apply Rnot_le_gt in H3.
       apply Rgt_minus; auto. }
    clear H4. apply der_str_moninc in pm.
    unfold strict_mon_increasing in pm.
    generalize (pm a b Domain_a_b); intro. 
    unfold plus_Fu in H4; unfold mult_real_f in H4.
    repeat rewrite Rmult_opp_1_l in H4.
    apply Rplus_lt_compat_r with(r:=G b) in H4.
    rewrite Rplus_assoc with(r1:=F b) in H4.
    rewrite Rplus_opp_l in H4; auto. rewrite Rplus_0_r in H4.
    apply Rplus_lt_compat_l with(r:=- F a) in H4.
    repeat rewrite <- Rplus_assoc in H4.
    rewrite Rplus_opp_l in H4; auto. rewrite Rplus_0_l in H4.
    rewrite Rplus_comm in H4. rewrite Rplus_comm with(r1:=-F a) in H4.
    apply Rlt_gt in H4. unfold Rminus in H1.
    apply Rgt_not_eq in H4. contradiction.
    intros; apply H3 in H4. unfold plus_Fu; unfold mult_real_f.
    rewrite Rmult_opp_1_l; unfold Rminus in H4; auto.
  - generalize(classic(exists v : R, v ∈ [a, b] /\ f v >= g v)); intro.
    destruct H2; auto.
    assert(~ (exists v, v ∈ [a, b] /\ f v >= g v) ->
     forall v, v ∈ [a, b] -> ~(f v >= g v)).
    { intros. unfold not; intro. destruct H3.
      exists v; split; auto. }
    generalize(H3 H2); intro. clear H3.
    assert(forall x, x ∈ [a, b] -> f x - g x < 0).
     { intros. apply H4 in H3. apply Rnot_ge_lt in H3.
       apply Rlt_minus; auto. }
    clear H4. apply der_str_mondec in pm.
    unfold strict_mon_decreasing in pm.
    generalize (pm a b Domain_a_b); intro.
    unfold plus_Fu in H4; unfold mult_real_f in H4.
    repeat rewrite Rmult_opp_1_l in H4.
    apply Rplus_lt_compat_r with(r:=G b) in H4.
    rewrite Rplus_assoc with(r1:=F b) in H4.
    rewrite Rplus_opp_l in H4; auto. rewrite Rplus_0_r in H4.
    apply Rplus_lt_compat_l with(r:=- F a) in H4.
    repeat rewrite <- Rplus_assoc in H4.
    rewrite Rplus_opp_l in H4; auto. rewrite Rplus_0_l in H4.
    rewrite Rplus_comm in H4. rewrite Rplus_comm with(r1:=-G a) in H4.
    unfold Rminus in H1. apply Rlt_not_eq in H4. contradiction.
    intros; apply H3 in H4.
    unfold plus_Fu; unfold mult_real_f.
    rewrite Rmult_opp_1_l; unfold Rminus in H4; auto.
Qed.


Lemma lemma4_4_2 : forall F f a b, a<b -> derivative F f a b ->
  exists u v, u ∈ [a,b] /\ v ∈ [a,b] /\ f u*(b-a)<=F b-F a <=f v *(b-a).
Proof.
  intros. apply Valuation_der with(F:=F)(G:=(fun x=>(F b-F a)*(x-a)/(b-a)))
                            (f:=f)(g:=fun x=>(F b -F a)/(b-a)) in H0; auto.
  destruct H0, H0, H0, H1.
  exists x,x0. split; auto. split; auto.
  - assert(0</(b - a)). 
     { apply Rinv_0_lt_compat; apply Rlt_Rminus; auto. }
    unfold Rdiv in H2. destruct H2. apply Rge_le in H4.
    split; apply Rmult_le_reg_r with (r:=/(b - a)); auto;
    rewrite Rinv_r_simpl_l; auto; apply Rminus_eq_contra;
    apply Rgt_not_eq; apply Rlt_gt; auto.
  - unfold derivative.
    exists (fun x => x); split.
    + split; intros.
      destruct H1, H2. apply Rlt_gt; auto.
      apply Rlt_le; auto.
    + split.
      * unfold bounded_rec_f; intros.
        generalize(Rgt_or_ge M 0); intro. destruct H1.
        -- assert(exists z : R, z ∈ (0, b - a] /\ z < 1/M).
            { assert(0<b-a). { apply Rlt_Rminus; auto. }
              generalize (total_order_T (1/M) (b-a)); intro.
              destruct H3. destruct s.
              - generalize(exist_Rgt_lt 0 (1/M)); intro. destruct H3.
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
        destruct H2, H2. exists x; split; auto.
        rewrite Rabs_right. destruct H2, H4.
        unfold Rdiv; rewrite Rmult_1_l.
        unfold Rdiv in H3; rewrite Rmult_1_l in H3.
        apply Rinv_lt_contravar in H3.
        rewrite Rinv_involutive in H3; auto.
        apply Rgt_not_eq; auto.
        apply Rmult_lt_0_compat; auto.
        apply Rinv_0_lt_compat; auto.
        unfold Rdiv; rewrite Rmult_1_l; apply Rgt_ge.
        destruct H2, H4.
        apply Rlt_gt; apply Rinv_0_lt_compat; auto.
        -- exists(b-a). repeat split; try apply Rlt_Rminus; auto.
           apply Req_le; auto.
           apply Rgt_ge_trans with(r1:=Rabs (1 / (b - a))) in H1; auto.
           apply Rabs_pos_lt. apply Rgt_not_eq. unfold Rdiv; rewrite Rmult_1_l.
           apply Rinv_0_lt_compat. apply Rlt_Rminus; auto.
      * exists 1. split. apply Rlt_0_1. intros.
        simpl. rewrite Rmult_1_l.
        rewrite <- Rinv_minus_distr_r.
        rewrite <- Rmult_minus_distr_l.
        assert((x + h - a - (x - a)=h)). { ring. }
        rewrite H2. clear H2. unfold Rdiv.
        rewrite Rmult_assoc. rewrite Rmult_comm with (r1:=h)(r2:=(/ (b - a))).
        rewrite <- Rmult_assoc. rewrite Rminus_diag_eq; auto.
        rewrite Rabs_R0. apply Rle_0_sqr.
        apply Rminus_eq_contra. apply Rgt_not_eq; apply Rlt_gt; auto.
  - rewrite Rminus_diag_eq with(r1:=a); auto.
    unfold Rdiv. rewrite Rmult_0_r; rewrite Rmult_0_l;
    rewrite Rminus_0_r. rewrite Rinv_r_simpl_l; auto.
    apply Rminus_eq_contra. apply Rgt_not_eq; apply Rlt_gt; auto.
Qed.


Lemma lemma4_3_1 : forall  r r1 r2, r<=r1 -> r1<=r2 ->
  Rabs r1 <= Rabs r \/ Rabs r1 <= Rabs r2.
Proof.
  intros.
  generalize (total_order_T r1 0); intro.
  destruct H1. destruct s.
  - cut (Rabs r1 <= Rabs r); auto.
    apply Ropp_le_contravar in H.
    apply Rsqr_incr_1 in H. repeat rewrite <- Rsqr_neg in H.
    apply Rsqr_le_abs_0; auto.
    apply Ropp_0_ge_le_contravar; apply Rgt_ge; auto.
    apply Rle_trans with (r2:= -r1); auto.
    apply Ropp_0_ge_le_contravar; apply Rgt_ge; auto.
  - rewrite e; rewrite Rabs_R0.
    generalize (Rabs_pos r); intro; auto.
  - cut (Rabs r1 <= Rabs r2); auto.
    apply Rsqr_le_abs_0. apply Rsqr_incr_1 in H0; auto.
    apply Rlt_le; auto.
    apply Rle_trans with (r2:=r1); auto.
    apply Rlt_le; auto.
Qed.

(* 若F在[a,b]上强可导，f(x)是F(x)的导数，则在[a,b]上有两点u、v，使得
  f(u)(b-a)>=F(b)-F(a)>=f(v)(b-a) *)
Lemma lemma4_3_2 : forall F f a b, a<b -> str_derivative F f a b ->
  exists u v, u ∈ [a,b] /\ v ∈ [a,b] /\ f u*(b-a)<= F b -F a <= f v * (b - a).
Proof.
  intros.
  apply lemma4_4_2; auto.
  apply strder_Deduce_der; auto.
Qed.


Theorem Theorem4_3 : forall F f a b,
  diff_quo_median F f a b /\
  (exists M, M>0 /\ forall x h, x ∈ [a,b] /\ (x+h) ∈ [a,b] ->
  Rabs(f(x+h) - f(x)) <= M*(Rabs h))
  <-> str_derivative F f a b.
Proof.
  intros.
  unfold diff_quo_median; unfold str_derivative.
  split.
  - intros. destruct H, H0, H0. rename x into M.
    exists M. split; auto; intros.
    generalize ( total_order_T h 0); intro.
    destruct H3. destruct s.
    + destruct H with (u:=x+h)(v:=x).
      unfold Rminus; rewrite Ropp_plus_distr; rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r; rewrite Rplus_0_l.
      generalize (Ropp_gt_lt_0_contravar h r); intro.
      split; tauto. destruct H3, H3, H4, H5.
      apply Rplus_le_compat_r with (r:=-f x)in H5.
      apply Rplus_le_compat_r with (r:=-f x)in H6.
      generalize (H1 x (x0-x)); intro.
      generalize (H1 x (x1-x)); intro.
      repeat rewrite Rplus_minus in H7.
      repeat rewrite Rplus_minus in H8.
      destruct H2.
      assert (x ∈ [a,b] /\ x0 ∈ [a,b]).
       { split; auto.
         unfold In; unfold cc.
         unfold In in H2, H3, H9; unfold cc in H2, H3, H9.
         destruct H2, H3, H9. split; auto.
         split.
         apply Rle_trans with(r2:=x+h); tauto.
         apply Rle_trans with (r2:=x); tauto. }
      assert (x ∈ [a,b] /\ x1 ∈ [a,b]).
       { split; auto.
         unfold In; unfold cc.
         unfold In in H2, H4, H9; unfold cc in H2, H4, H9.
         destruct H2, H4, H9. split; auto.
         split.
         apply Rle_trans with(r2:=x+h); tauto.
         apply Rle_trans with (r2:=x); tauto. }
      assert(Rabs((F x-F(x+h))/(x-(x+h))+-f x) <= Rabs(f x0 + - f x) \/
        Rabs((F x-F(x+h))/(x-(x+h))+-f x) <= Rabs(f x1+-f x)).
       { apply lemma4_3_1; auto. }
      apply H7 in H10; apply H8 in H11.
      destruct H12.
      * assert(h<>0) as l. { apply Rlt_not_eq; auto. }
        assert(Rabs((F x-F(x+h))/(x-(x+h))+-f x)<=M*Rabs(x0-x)).
         { apply Rle_trans with (r2:=Rabs (f x0 - f x)); auto. }
        unfold Rminus in H13. rewrite Ropp_plus_distr in H13;
        rewrite <- Rplus_assoc in H13.
        rewrite Rplus_opp_r in H13; rewrite Rplus_0_l in H13.
        unfold Rdiv in H13. rewrite <- Ropp_inv_permute in H13; auto.
        rewrite <- Ropp_mult_distr_r in H13; rewrite Ropp_mult_distr_l in H13.
        rewrite Ropp_plus_distr in H13; rewrite Ropp_involutive in H13.
        rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        repeat rewrite Rmult_assoc;
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r;
        rewrite Rplus_comm with(r1:=F(x+h)).
        apply Rle_trans with (r2:=M*Rabs (x0 + - x)); auto.
        apply Rmult_le_compat_l. apply Rlt_le; auto.
        unfold In in H2; unfold cc in H2; destruct H2.
        repeat rewrite Rabs_left1.
        apply Ropp_le_contravar; apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        unfold In in H3; unfold cc in H3. tauto.
        apply Rlt_le; auto.
        apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        rewrite Rplus_0_r.
        unfold In in H3; unfold cc in H3; tauto.
      * assert(h<>0) as l. { apply Rlt_not_eq; auto. }
        assert(Rabs((F x-F(x+h))/(x-(x+h))+-f x)<=M*Rabs(x1-x)).
        { apply Rle_trans with (r2:=Rabs (f x1 - f x)); auto. }
        unfold Rminus in H13.
        rewrite Ropp_plus_distr in H13; rewrite <- Rplus_assoc in H13.
        rewrite Rplus_opp_r in H13; rewrite Rplus_0_l in H13.
        unfold Rdiv in H13. rewrite <- Ropp_inv_permute in H13; auto.
        rewrite <- Ropp_mult_distr_r in H13; rewrite Ropp_mult_distr_l in H13.
        rewrite Ropp_plus_distr in H13; rewrite Ropp_involutive in H13.
        rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        repeat rewrite Rmult_assoc; repeat rewrite <- Rabs_mult;
        rewrite Rinv_r; auto; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r;
        rewrite Rplus_comm with(r1:=F(x+h)).
        apply Rle_trans with (r2:=M*Rabs (x1 + - x)); auto.
        apply Rmult_le_compat_l. apply Rlt_le; auto.
        unfold In in H2; unfold cc in H2; destruct H2.
        repeat rewrite Rabs_left1.
        apply Ropp_le_contravar; apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        unfold In in H4; unfold cc in H4. tauto.
        apply Rlt_le; auto.
        apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        rewrite Rplus_0_r.
        unfold In in H4; unfold cc in H4; tauto.
   + rewrite e.
     rewrite Rplus_0_r; rewrite Rmult_0_r; rewrite Rminus_0_r; rewrite Rminus_diag_eq; auto.
     rewrite <- Rsqr_pow2; rewrite Rsqr_0; rewrite Rmult_0_r; rewrite Rabs_R0;
     apply Req_le_sym; auto.
   + destruct H2. destruct H with (u:=x)(v:=x+h).
     rewrite <- R_distr; rewrite Rminus_diag_eq; auto; rewrite Rplus_0_l.
     split; auto.
     destruct H4, H4, H5, H6.
     apply Rplus_le_compat_r with (r:=-f x)in H6.
     apply Rplus_le_compat_r with (r:=-f x)in H7.
     generalize (H1 x (x0-x)); intro.
     generalize (H1 x (x1-x)); intro.
     repeat rewrite Rplus_minus in H8.
     repeat rewrite Rplus_minus in H9.
     assert (x ∈ [a,b] /\ x0 ∈ [a,b]).
      { split; auto.
        unfold In; unfold cc.
        unfold In in H2, H3, H4; unfold cc in H2, H3, H4.
        destruct H2, H3, H4. split; auto.
        split.
        apply Rle_trans with(r2:=x); tauto.
        apply Rle_trans with (r2:=x+h); tauto. }
     assert (x ∈ [a,b] /\ x1 ∈ [a,b]).
      { split; auto.
        unfold In; unfold cc.
        unfold In in H2, H3, H5; unfold cc in H2, H3, H5.
        destruct H2, H3, H5. split; auto.
        split.
        apply Rle_trans with(r2:=x); tauto.
        apply Rle_trans with (r2:=x+h); tauto. }
     assert(Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=Rabs(f x0+-f x) \/
            Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=Rabs(f x1+-f x)).
      { apply lemma4_3_1; auto. }
     apply H8 in H10; apply H9 in H11.
     destruct H12.
     * assert(h<>0) as l. { apply Rgt_not_eq; auto. }
       assert(Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=M*Rabs(x0-x)).
        { apply Rle_trans with (r2:=Rabs (f x0 - f x)); auto. }
       rewrite <- R_distr in H13.
       rewrite Rminus_diag_eq with (r1:=x)(r2:=x)in H13; auto;
       rewrite Rplus_0_l in H13.
       rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
       apply Rmult_le_reg_r with (r:=Rabs (/h)).
       apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rgt_not_eq; auto.
       repeat rewrite Rmult_assoc; repeat rewrite <- Rabs_mult;
       rewrite Rinv_r; auto;
       rewrite Rmult_1_r.
       unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
       rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
       unfold Rminus in H13; apply Rle_trans with (r2:=M*Rabs (x0 + - x)); auto.
       apply Rmult_le_compat_l. apply Rlt_le; auto.
       unfold In in H4; unfold cc in H4; destruct H4.
       repeat rewrite Rabs_right.
       apply Rplus_le_reg_r with (r:=x).
       rewrite Rplus_assoc; rewrite Rplus_opp_l;
       rewrite Rplus_0_r; rewrite Rplus_comm. tauto.
       apply Rgt_ge; auto.
       apply Rplus_ge_reg_l with (r:=x).
       rewrite Rplus_0_r. rewrite Rplus_comm; rewrite Rplus_assoc.
       rewrite Rplus_opp_l; rewrite Rplus_0_r. apply Rle_ge; tauto.
     * assert(h<>0) as l. { apply Rgt_not_eq; auto. }
       assert(Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=M*Rabs(x1-x)).
        { apply Rle_trans with (r2:=Rabs (f x1 - f x)); auto. }
       rewrite <- R_distr in H13.
       rewrite Rminus_diag_eq with (r1:=x)(r2:=x)in H13; auto;
       rewrite Rplus_0_l in H13.
       rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
       apply Rmult_le_reg_r with (r:=Rabs (/h)).
       apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rgt_not_eq; auto.
       repeat rewrite Rmult_assoc; repeat rewrite <- Rabs_mult;
       rewrite Rinv_r; auto; rewrite Rmult_1_r.
       unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
       rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
       unfold Rminus in H13; apply Rle_trans with (r2:=M*Rabs (x1 + - x)); auto.
       apply Rmult_le_compat_l. apply Rlt_le; auto.
       unfold In in H5; unfold cc in H5; destruct H5.
       repeat rewrite Rabs_right.
       apply Rplus_le_reg_r with (r:=x).
       rewrite Rplus_assoc; rewrite Rplus_opp_l;
       rewrite Rplus_0_r; rewrite Rplus_comm. tauto.
       apply Rgt_ge; auto.
       apply Rplus_ge_reg_l with (r:=x).
       rewrite Rplus_0_r. rewrite Rplus_comm; rewrite Rplus_assoc.
       rewrite Rplus_opp_l; rewrite Rplus_0_r. apply Rle_ge; tauto.
  - split; intros.
    destruct H, H. rename x into M.
    + assert(str_derivative F f u v).
       { unfold str_derivative; intros.
         exists M; split; auto.
         intros.
         assert(x ∈ [a,b] /\ (x + h) ∈ [a,b]).
          { unfold In; unfold cc.
            destruct H0, H3, H2.
            unfold In in H0, H3, H2, H5; unfold cc in H0, H3, H2, H5.
            destruct H0, H3, H2, H5.
            repeat split; auto.
            apply Rle_trans with (r2:=u); tauto.
            apply Rle_trans with (r2:=v); tauto.
            apply Rle_trans with (r2:=u); tauto.
            apply Rle_trans with (r2:=v); tauto. }
         apply H1 in H3; auto. }
      apply lemma4_3_2 in H2.
      destruct H2, H2, H2, H3.
      exists x, x0; split; auto. split; auto.
      apply Rinv_le_r with (r:=(v-u)) in H4.
      assert (v - u <> 0). { apply Rgt_not_eq; tauto. }
      unfold Rdiv in H4; rewrite Rinv_r_simpl_l in H4;
      rewrite Rinv_r_simpl_l in H4; auto.
      tauto.
      apply Rgt_lt; apply Rminus_gt; tauto.
    + destruct H, H. rename x into M.
      exists (2*M).
      split. apply Rmult_lt_0_compat; auto. apply Rlt_0_2.
      intros.
      generalize (H0 (x+h) (-h)); intro.
      assert((x+h) ∈ [a,b] /\ x ∈ [a,b]). { split; tauto. }
      rewrite Rplus_assoc in H2; rewrite Rplus_opp_r in H2;
      rewrite Rplus_0_r in H2.
      apply H0 in H1; apply H2 in H3. clear H2.
      rewrite <- Rsqr_pow2 in H3; rewrite <- Rsqr_neg in H3;
      rewrite <- Rsqr_pow2 in H1.
      apply Rplus_le_compat with (r1:=Rabs (F x - F (x + h) - f (x + h) * - h))
                                 (r2:=M * h²) in H1; auto.
      generalize(Rabs_triang (F x-F(x+h)-f(x+h)*-h)(F(x+h)-F x-f x*h)); intro.
      apply Rle_trans with (r3:=M * h² + M * h²) in H2; auto.
      rewrite <- plus_ab_minus_cd in H2. rewrite Rplus_comm with(r1:=F x) in H2.
      rewrite Rminus_diag_eq with (r1:=F (x + h) + F x)in H2; auto.
      rewrite Rminus_0_l in H2; rewrite Ropp_plus_distr in H2.
      rewrite Ropp_mult_distr_l in H2; rewrite Rmult_opp_opp in H2.
      rewrite Ropp_mult_distr_l in H2.
      repeat rewrite <- Rmult_plus_distr_r in H2.
      rewrite Rsqr_abs in H2; unfold Rsqr in H2; rewrite <- Rmult_assoc in H2.
      rewrite Rabs_mult in H2. rewrite double.
      generalize(Rabs_pos h); intro.
      destruct H4.
      * apply Rmult_le_reg_r with(r:=Rabs h); auto.
      * rewrite <- Rabs_R0 in H4; apply Rsqr_eq_asb_1 in H4;
        rewrite Rsqr_0 in H4.
        apply eq_sym in H4. apply Rsqr_eq_0 in H4.
        rewrite H4; rewrite Rplus_0_r. rewrite Rabs_R0; rewrite Rmult_0_r.
        rewrite Rminus_diag_eq; auto. rewrite Rabs_R0. apply Req_le_sym; auto.
Qed.


(* 若 F 在[a , b] 上一致可导, f(x)是 F(x)的导数,则在[ a , b] 上有两点 u、v ,使得
     f(u)*(b-a)<=F(b)-F(a)<=f(v)*(b-a) *)

Lemma lemma4_4_1 : forall F f a b, derivative F f a b ->
  forall u v , u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 -> derivative F f u v.
Proof.
  intros.
  unfold derivative; unfold derivative in H.
  destruct H. rename x into d.
  destruct H, H1, H2, H2. rename x into M.
  exists d.
  assert (forall z, z ∈ (0, v - u] -> z ∈ (0, b - a]).
   { intros.
     unfold In; unfold oc; unfold In in H4; unfold oc in H4.
     destruct H0.
     unfold In in H0; unfold cc in H0.
     destruct H0, H6, H5, H5, H9, H4, H11.
     repeat split; auto.
     apply Rlt_Rminus; auto.
     apply Rle_trans with(r2:=v - u); auto.
     unfold Rminus; apply Rplus_le_compat. tauto.
     apply Ropp_le_contravar; tauto. }
  assert((v - u) ∈ (0, v - u]) as l1.
   { unfold In; unfold oc.
      repeat split; try apply Rgt_lt; try tauto.
      apply Rge_refl. }
  split.
  - unfold pos_inc; unfold pos_inc in H.
    split.
    + intros.
      apply H4 in H5. apply H; auto.
    + intros.
      apply H4 in H5; apply H4 in H6.
      apply H; auto.
  - split.
    + unfold bounded_rec_f; unfold bounded_rec_f in H1.
      intros.
      generalize(H1 M0); intro. destruct H5.
      assert(x ∈ (0, b - a] -> x ∈ (0, v - u] \/ x ∈ (v - u, b - a]).
       { intro.
         unfold In; unfold oc.
         generalize (classic (0 < x <= v - u)); intro.
         destruct H7.
         left. split; try apply Rgt_lt; auto. tauto.
         right. apply not_and_or in H7.
         unfold In in H6; unfold oc in H6.
         destruct H6, H8, H7. contradiction.
         apply Rnot_le_lt in H7.
         repeat split; auto.
         apply Rlt_le_trans with(r2:=x); auto. }
      destruct H5; generalize H5 as l2; intro; apply H6 in H5; destruct H5.
      exists x; split; auto.
      exists (v-u); split; auto.
      unfold pos_inc in H; destruct H.
      destruct H5, H9.
      apply H8 in H9; auto.
      apply H4 in l1; apply H in l1.
      apply H in l2.
      apply Rlt_le_trans with (r2:=Rabs (1 / d x)); auto.
      unfold Rdiv. repeat rewrite Rmult_1_l.
      repeat rewrite Rabs_pos_eq.
      apply Rle_Rinv; auto.
      apply Rlt_le; apply Rinv_0_lt_compat; auto.
      apply Rlt_le; apply Rinv_0_lt_compat; auto.
    + exists M; split; auto.
      intros.
      assert(forall x, x ∈ [u, v] -> x ∈ [a, b]).
       { intros.
         unfold In; unfold cc; unfold In in H6; unfold cc in H6.
         destruct H0, H7.
         unfold In in H0, H7; unfold cc in H0, H7.
         destruct H0, H9, H7, H11, H6, H13.
         repeat split; auto.
         apply Rle_trans with(r2:=u); auto.
         apply Rle_trans with(r2:=v); auto. }
      apply H3.
      destruct H5, H7.
      apply H6 in H5; apply H6 in H7.
      split; auto.
Qed.


Theorem Theorem4_4 : forall F f a b, derivative F f a b <->
  diff_quo_median F f a b /\ uniform_continuous f a b.
Proof.
  intros.
  split; intros.
  - split.
    + unfold diff_quo_median; intros.
      apply lemma4_4_1 with (u:=u)(v:=v)in H; auto.
      apply lemma4_4_2 in H.
      destruct H, H, H, H1.
      exists x, x0. split; auto. split; auto.
      apply Rmult_le_r with (r:=(v-u)). tauto.
      unfold Rdiv; rewrite Rinv_mult_rgt0; auto; tauto.
      apply Rgt_lt; apply Rminus_gt; tauto.
    + unfold derivative in H; unfold uniform_continuous.
      destruct H, H, H0, H1, H1. rename x into d; rename x0 into M.
      exists (mult_real_f (2*M) d).
      assert(0<2*M) as l. { apply Rmult_gt_0_compat; auto. apply Rlt_0_2. }
      split.
       * unfold pos_inc; unfold pos_inc in H. 
         destruct H; split; intros.
         apply H in H4; unfold mult_real_f.
         apply Rmult_gt_0_compat; auto.
         unfold mult_real_f.
         apply (H3 z1) in H5; auto.
         apply (Rmult_le_compat_l (2*M)); auto.
         apply Rlt_le; auto.
       * split.
         -- unfold bounded_rec_f; unfold mult_real_f; intros.
            unfold bounded_rec_f in H0.
            destruct H0 with (M:=2*M*M0).
            destruct H3. exists x. split; auto.
            apply (Rmult_lt_reg_l (2*M)); auto.
            rewrite <- Rabs_right with(r:=2*M) at 2.
            rewrite <- Rabs_mult.
            assert(2*M<>0). { apply Rgt_not_eq; auto. }
            unfold Rdiv; rewrite Rinv_mult_distr; auto. rewrite Rmult_1_l.
            rewrite <- Rmult_assoc; rewrite Rinv_r; auto.
            unfold pos_inc in H. destruct H. apply H in H3.
            apply Rgt_not_eq; auto.
            apply Rgt_ge; auto.
         -- intros.
            assert(h<>0) as p. { tauto. }
            assert((x+h) ∈ [a,b] /\ x ∈ [a,b] /\ -h <> 0).
             { split. tauto. split. tauto. apply Ropp_neq_0_compat; tauto. }
            apply H2 in H3.
            generalize(H2 (x+h) (-h)); intro.
            rewrite Rplus_assoc in H5; rewrite Rplus_opp_r in H5;
            rewrite Rplus_0_r in H5.
            apply H5 in H4; clear H5.
            rewrite Rabs_Ropp in H4.
            apply Rplus_le_compat with (r1:=Rabs (F x-F(x+h)-f(x+h)*-h))
                                 (r2:=M*Rabs h * d (Rabs h)) in H3; auto.
            generalize(Rabs_triang (F x-F(x+h)-f(x+h)*-h)(F(x+h)-F x-f x*h));
            intro.
            rewrite <- double in H3.
            apply Rle_trans with (r3:=2 * (M * Rabs h * d (Rabs h))) in H5; auto.
            rewrite <- plus_ab_minus_cd in H5.
            rewrite Rplus_comm with(r1:=F x) in H5.
            rewrite Rminus_diag_eq with (r1:=F (x + h) + F x)in H5; auto.
            rewrite Rminus_0_l in H5; rewrite Ropp_plus_distr in H5.
            rewrite Ropp_mult_distr_l in H5; rewrite Rmult_opp_opp in H5.
            rewrite Ropp_mult_distr_l in H5;
            repeat rewrite <- Rmult_plus_distr_r in H5.
            rewrite Rabs_mult in H5.
            rewrite Rmult_assoc in H5.
            rewrite (Rmult_comm (Rabs h)(d(Rabs h))) in H5.
            repeat rewrite <- Rmult_assoc in H5.  
            unfold mult_real_f.
            generalize(Rabs_pos h); intro.
            destruct H6.
            apply Rmult_le_reg_r with(r:=Rabs h); auto.
            rewrite <- Rabs_R0 in H6; apply Rsqr_eq_asb_1 in H6;
            rewrite Rsqr_0 in H6.
            apply eq_sym in H6.  apply Rsqr_eq_0 in H6. destruct p; auto.
  - destruct H.
    unfold diff_quo_median in H; unfold uniform_continuous in H0.
    unfold derivative.
    destruct H0, H0, H1. rename x into d.
    exists d. split; auto. split; auto.
    exists 1. split. apply Rlt_0_1. intros.
    rewrite Rmult_1_l.
    assert(h<0\/h>0) as l.
     { apply Rdichotomy; tauto. }
    destruct H3, H4, l.
    assert((x+h) ∈ [a,b]/\ x ∈ [a,b] /\ x-(x+h)>0).
     { split; auto. split; auto.
       unfold Rminus; rewrite Ropp_plus_distr.
       rewrite <- Rplus_assoc; rewrite Rplus_opp_r.
       rewrite Rplus_0_l. apply Ropp_gt_lt_0_contravar; auto. }
    apply H in H7.
    destruct H7, H7, H7, H8, H9.
    apply Rplus_le_compat_r with (r:=-f x)in H9.
    apply Rplus_le_compat_r with (r:=-f x)in H10.
    generalize (Req_dec x0 x); intro.
    destruct H11.
    + generalize (Req_dec x1 x); intro.
      destruct H12.
      * rewrite H11 in H9; rewrite H12 in H10.
        rewrite Rplus_opp_r in H9. rewrite Rplus_opp_r in H10.
        apply Rle_antisym in H9; auto.
        unfold Rminus in H9; rewrite Ropp_plus_distr in H9.
        rewrite <- Rplus_assoc in H9; rewrite Rplus_opp_r in H9.
        rewrite Rplus_0_l in H9.
        unfold Rdiv in H9; rewrite <- Ropp_inv_permute in H9; auto.
        rewrite <- Ropp_mult_distr_r in H9; rewrite Ropp_mult_distr_l in H9.
        rewrite Ropp_plus_distr in H9; rewrite Ropp_involutive in H9.
        rewrite Rplus_comm with(r1:=-F x) in H9.
        apply Rmult_eq_compat_r with(r:=h) in H9.
        rewrite Rmult_plus_distr_r in H9; rewrite Rmult_0_l in H9.
        rewrite Rmult_assoc in H9; rewrite Rinv_l in H9; auto.
        rewrite Rmult_1_r in H9.
        unfold Rminus; rewrite Ropp_mult_distr_l; rewrite H9.
        rewrite Rabs_R0.
        apply Rmult_le_pos. apply Rabs_pos.
        unfold pos_inc in H0; destruct H0.
        apply Rlt_le; apply H0.
        unfold In; unfold oc.
        unfold In in H3, H4; unfold cc in H3, H4.
        destruct H3, H4.
        split. apply Rlt_Rminus; auto.
        split. apply Rabs_pos_lt; auto.
        rewrite Rabs_left; auto.
        apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
        rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
        rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
        destruct H14, H15.
        apply Rle_trans with(r2:=x+h); auto.
        apply Rplus_le_compat_r; auto.
      * rewrite H11 in H9; rewrite Rplus_opp_r in H9.
        assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a,b] /\ x1-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
        apply H2 in H13. generalize H9; intro.
        apply Rle_trans with(r3:= f x1 + - f x) in H9; auto.
        rewrite <- Rabs_right in H10.
        rewrite <- Rabs_right with(r:=(F x-F(x+h))/(x-(x+h))+-f x) in H10.
        unfold Rminus in H10; rewrite Ropp_plus_distr in H10.
        rewrite <- Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
        rewrite Rplus_0_l in H10.
        unfold Rdiv in H10; rewrite <- Ropp_inv_permute in H10; auto.
        rewrite <- Ropp_mult_distr_r in H10; rewrite Ropp_mult_distr_l in H10.
        rewrite Ropp_plus_distr in H10; rewrite Ropp_involutive in H10.
        rewrite Rplus_comm with(r1:=-F x) in H10.
        rewrite Rplus_minus in H13.
        apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
        rewrite Rabs_R1; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
        unfold pos_inc in H0; destruct H0.
        assert((Rabs(x1-x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\Rabs(x1-x)<=Rabs h).
         { split; unfold In; unfold oc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_left1. rewrite Ropp_minus_distr.
           unfold Rminus; apply Rplus_le_compat. tauto.
           apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_minus; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_left; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
           rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
           destruct H16, H17.
           apply Rle_trans with(r2:=x+h); auto.
           apply Rplus_le_compat_r; auto.
           unfold In in H8; unfold cc in H8. destruct H8.
           rewrite Rabs_left1. rewrite Rabs_left; auto.
           apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rle_minus; tauto. }
        destruct H16, H17, H18.
        apply H15 in H18; auto.
        right; rewrite H18; auto.
        apply Rle_ge; auto. apply Rle_ge; auto.
    + generalize (Req_dec x1 x); intro.
      destruct H12.
      * rewrite H12 in H10; rewrite Rplus_opp_r in H10.
        assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
        apply H2 in H13. generalize H9; intro.
        apply Rle_trans with(r3:= 0) in H9; auto.
        rewrite <- Ropp_involutive with(r:=f x0 + - f x) in H14.
        rewrite <- Rabs_right with(r:=-(f x0 + - f x)) in H14.
        rewrite <- Ropp_involutive with(r:=(F x-F(x+h))/(x-(x+h))+-f x) in H14.
        rewrite <- Rabs_right with(r:=-((F x-F(x+h))/(x-(x+h))+-f x)) in H14.
        apply Ropp_le_cancel in H14.
        repeat rewrite Rabs_Ropp in H14.
        unfold Rminus in H14; rewrite Ropp_plus_distr in H14.
        rewrite <- Rplus_assoc in H14; rewrite Rplus_opp_r in H14.
        rewrite Rplus_0_l in H14.
        unfold Rdiv in H14; rewrite <- Ropp_inv_permute in H14; auto.
        rewrite <- Ropp_mult_distr_r in H14; rewrite Ropp_mult_distr_l in H14.
        rewrite Ropp_plus_distr in H14; rewrite Ropp_involutive in H14.
        rewrite Rplus_comm with(r1:=-F x) in H14.
        rewrite Rplus_minus in H13.
        apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H14; auto.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
        rewrite Rabs_R1; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
        unfold pos_inc in H0; destruct H0.
        assert((Rabs(x0-x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\Rabs(x0-x)<=Rabs h).
         { split; unfold In; unfold oc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H7.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_left1. rewrite Ropp_minus_distr.
           unfold Rminus; apply Rplus_le_compat. tauto.
           apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_minus; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_left; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
           rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
           destruct H16, H17.
           apply Rle_trans with(r2:=x+h); auto.
           apply Rplus_le_compat_r; auto.
           unfold In in H7; unfold cc in H7. destruct H7.
           rewrite Rabs_left1. rewrite Rabs_left; auto.
           apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rle_minus; tauto. }
        destruct H16, H17, H18.
        apply H15 in H18; auto.
        right; rewrite H18; auto.
        rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
        rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
      * assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a, b] /\ x1-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
         assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
         apply H2 in H13; apply H2 in H14.
         apply lemma4_3_1 with(r:=f x0 + - f x) in H10; auto.
         destruct H10.
         -- unfold Rminus in H10; rewrite Ropp_plus_distr in H10.
            rewrite <- Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
            rewrite Rplus_0_l in H10.
            unfold Rdiv in H10; rewrite <- Ropp_inv_permute in H10; auto.
            rewrite <- Ropp_mult_distr_r in H10;
            rewrite Ropp_mult_distr_l in H10.
            rewrite Ropp_plus_distr in H10; rewrite Ropp_involutive in H10.
            rewrite Rplus_comm with(r1:=-F x) in H10.
            rewrite Rplus_minus in H14.
            apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs (x0 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
                   Rabs (x0 - x)<=Rabs h).
             { split; unfold In; unfold oc.
               unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
               destruct H3, H4, H7.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
               rewrite Rabs_left1. rewrite Ropp_minus_distr.
               unfold Rminus; apply Rplus_le_compat. tauto.
               apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
               apply Rle_minus; tauto.
               unfold In in H3, H4; unfold cc in H3, H4.
               destruct H3, H4.
               split.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; auto.
               rewrite Rabs_left; auto.
               apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
               rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
               rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
               destruct H16, H17.
               apply Rle_trans with(r2:=x+h); auto.
               apply Rplus_le_compat_r; auto.
               unfold In in H7; unfold cc in H7. destruct H7.
               rewrite Rabs_left1. rewrite Rabs_left; auto.
               apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
               rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
               apply Rle_minus; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
         -- unfold Rminus in H10; rewrite Ropp_plus_distr in H10.
            rewrite <- Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
            rewrite Rplus_0_l in H10.
            unfold Rdiv in H10; rewrite <- Ropp_inv_permute in H10; auto.
            rewrite <- Ropp_mult_distr_r in H10;
            rewrite Ropp_mult_distr_l in H10.
            rewrite Ropp_plus_distr in H10; rewrite Ropp_involutive in H10.
            rewrite Rplus_comm with(r1:=-F x) in H10.
            rewrite Rplus_minus in H13.
            apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus. rewrite Rmult_plus_distr_r;
            rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs (x1 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
                   Rabs (x1 - x)<=Rabs h).
            { split; unfold In; unfold oc.
              unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
              destruct H3, H4, H8.
              split. apply Rlt_Rminus; auto.
              split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
              rewrite Rabs_left1. rewrite Ropp_minus_distr.
              unfold Rminus; apply Rplus_le_compat. tauto.
              apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
              apply Rle_minus; tauto.
              unfold In in H3, H4; unfold cc in H3, H4.
              destruct H3, H4.
              split.
              split. apply Rlt_Rminus; auto.
              split. apply Rabs_pos_lt; auto.
              rewrite Rabs_left; auto.
              apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
              rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
              rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
              destruct H16, H17.
              apply Rle_trans with(r2:=x+h); auto.
              apply Rplus_le_compat_r; auto.
              unfold In in H8; unfold cc in H8. destruct H8.
              rewrite Rabs_left1. rewrite Rabs_left; auto.
              apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
              rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
              apply Rle_minus; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
    + assert(x ∈ [a,b] /\ (x+h) ∈ [a,b] /\ (x+h)-x>0).
       { split; auto. split; auto.
         rewrite <- R_distr.
         unfold Rminus; rewrite Rplus_opp_r; rewrite Rplus_0_l; auto. }
      apply H in H7.
      destruct H7, H7, H7, H8, H9.
      apply Rplus_le_compat_r with (r:=-f x)in H9.
      apply Rplus_le_compat_r with (r:=-f x)in H10.
      generalize (Req_dec x0 x); intro.
      destruct H11.
      * generalize (Req_dec x1 x); intro.
        destruct H12.
        -- rewrite H11 in H9; rewrite H12 in H10.
           rewrite Rplus_opp_r in H9. rewrite Rplus_opp_r in H10.
           apply Rle_antisym in H9; auto.
           rewrite <- R_distr in H9.
           unfold Rminus in H9; rewrite Rplus_opp_r in H9;
           rewrite Rplus_0_l in H9.
           unfold Rdiv in H9; apply Rmult_eq_compat_r with(r:=h) in H9.
           rewrite Rmult_plus_distr_r in H9; rewrite Rmult_0_l in H9.
           rewrite Rmult_assoc in H9; rewrite Rinv_l in H9; auto.
           rewrite Rmult_1_r in H9.
           unfold Rminus; rewrite Ropp_mult_distr_l; rewrite H9.
           rewrite Rabs_R0.
           apply Rmult_le_pos. apply Rabs_pos.
           unfold pos_inc in H0; destruct H0.
           apply Rlt_le; apply H0.
           unfold In; unfold oc.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_right; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm; apply Rle_trans with(r2:=x+h).
           apply Rplus_le_compat_r with(r:=h); tauto. tauto.
           apply Rgt_ge; auto.
        -- rewrite H11 in H9; rewrite Rplus_opp_r in H9.
           assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a,b] /\ x1-x<>0).
            { split; auto.
              split.
              unfold In; unfold cc.
              unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
              destruct H3, H4, H8. split; auto.
              rewrite Rplus_minus. split.
              apply Rle_trans with(r2:=x); tauto.
              apply Rle_trans with (r2:=x+h); tauto.
              apply Rminus_eq_contra; auto. }
           apply H2 in H13. generalize H9; intro.
           apply Rle_trans with(r3:= f x1 + - f x) in H9; auto.
        rewrite <- Rabs_right in H10.
        rewrite <- Rabs_right with(r:=(F(x+h)-F x)/((x+h)-x)+-f x) in H10.
        rewrite <- R_distr in H10.
        unfold Rminus in H10; rewrite Rplus_opp_r in H10;
        rewrite Rplus_0_l in H10.
        rewrite Rplus_minus in H13.
        apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
        rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
        rewrite Rabs_R1; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
        unfold pos_inc in H0; destruct H0.
        assert((Rabs(x1-x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\Rabs(x1-x)<=Rabs h).
         { split; unfold In; unfold oc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_right.
           unfold Rminus; apply Rplus_le_compat.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Ropp_le_contravar; tauto.
           apply Rge_minus; apply Rle_ge; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_right; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm.
           apply Rle_trans with(r2:=x+h).
           apply Rplus_le_compat_r; tauto. tauto.
           apply Rgt_ge; auto.
           unfold In in H8; unfold cc in H8; destruct H8.
           rewrite Rabs_right. rewrite Rabs_right.
           apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rgt_ge; auto.
           apply Rge_minus; apply Rle_ge; tauto. }
         destruct H16, H17, H18.
         apply H15 in H18; auto.
         right; rewrite H18; auto.
         apply Rle_ge; auto.
         apply Rle_ge; auto.
     * generalize (Req_dec x1 x); intro.
       destruct H12.
       -- rewrite H12 in H10; rewrite Rplus_opp_r in H10.
          assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
           { split; auto.
             split.
             unfold In; unfold cc.
             unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
             destruct H3, H4, H8. split; auto.
             rewrite Rplus_minus. split.
             apply Rle_trans with(r2:=x); tauto.
             apply Rle_trans with (r2:=x+h); tauto.
             apply Rminus_eq_contra; auto. }
           apply H2 in H13. generalize H9; intro.
           apply Rle_trans with(r3:= 0) in H9; auto.
           rewrite <- Ropp_involutive with(r:=f x0 + - f x) in H14.
           rewrite <- Rabs_right with(r:=-(f x0 + - f x)) in H14.
           rewrite<-Ropp_involutive with(r:=(F(x+h)-F x)/((x+h)-x)+-f x) in H14.
           rewrite <- Rabs_right with(r:=-((F(x+h)-F x)/((x+h)-x)+-f x)) in H14.
           apply Ropp_le_cancel in H14.
           repeat rewrite Rabs_Ropp in H14.
           rewrite <- R_distr in H14.
           unfold Rminus in H14; rewrite Rplus_opp_r in H14;
           rewrite Rplus_0_l in H14.
           rewrite Rplus_minus in H13.
           apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H14; auto.
           apply Rmult_le_reg_r with (r:=Rabs (/h)).
           apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
           rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
           repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
           rewrite Rabs_R1; rewrite Rmult_1_r.
           unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
           rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
           apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
           unfold pos_inc in H0; destruct H0.
           assert((Rabs (x0 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
                  Rabs (x0 - x)<=Rabs h).
            { split; unfold In; unfold oc.
              unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
              destruct H3, H4, H7.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_right.
           unfold Rminus; apply Rplus_le_compat.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Ropp_le_contravar; tauto.
           apply Rge_minus; apply Rle_ge; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_right; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm.
           apply Rle_trans with(r2:=x+h).
           apply Rplus_le_compat_r; tauto. tauto.
           apply Rgt_ge; auto.
           unfold In in H7; unfold cc in H7; destruct H7.
           rewrite Rabs_right. rewrite Rabs_right.
           apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rgt_ge; auto.
           apply Rge_minus; apply Rle_ge; tauto. }
         destruct H16, H17, H18.
         apply H15 in H18; auto.
         right; rewrite H18; auto.
         rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
         rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
      -- assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a,b] /\ x1-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x); tauto.
           apply Rle_trans with (r2:=x+h); tauto.
           apply Rminus_eq_contra; auto. }
         assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x); tauto.
           apply Rle_trans with (r2:=x+h); tauto.
           apply Rminus_eq_contra; auto. }
         apply H2 in H13; apply H2 in H14.
         apply lemma4_3_1 with(r:=f x0 + - f x) in H10; auto.
         destruct H10.
         ++ rewrite <- R_distr in H10.
            unfold Rminus in H10; rewrite Rplus_opp_r in H10;
            rewrite Rplus_0_l in H10.
            rewrite Rplus_minus in H14.
            apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus. rewrite Rmult_plus_distr_r;
            rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs (x0 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
              Rabs (x0 - x)<=Rabs h).
             { split; unfold In; unfold oc.
               unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
               destruct H3, H4, H7.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
               rewrite Rabs_right.
               unfold Rminus; apply Rplus_le_compat.
               apply Rle_trans with(r2:=x+h); tauto.
               apply Ropp_le_contravar; tauto.
               apply Rge_minus; apply Rle_ge; tauto.
               unfold In in H3, H4; unfold cc in H3, H4.
               destruct H3, H4.
               split.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; auto.
               rewrite Rabs_right; auto.
               apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
               rewrite Rplus_comm.
               apply Rle_trans with(r2:=x+h).
               apply Rplus_le_compat_r; tauto. tauto.
               apply Rgt_ge; auto.
               unfold In in H7; unfold cc in H7; destruct H7.
               rewrite Rabs_right. rewrite Rabs_right.
               apply Rplus_le_reg_r with(r:=x).
               rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
               apply Rgt_ge; auto.
               apply Rge_minus; apply Rle_ge; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
         ++ rewrite <- R_distr in H10.
            unfold Rminus in H10; rewrite Rplus_opp_r in H10;
            rewrite Rplus_0_l in H10.
            rewrite Rplus_minus in H13.
            apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus.
            rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs(x1-x))∈(0,b-a]/\(Rabs h)∈(0,b-a]/\Rabs(x1-x)<=Rabs h).
             { split; unfold In; unfold oc.
               unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
               destruct H3, H4, H8.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
               rewrite Rabs_right.
               unfold Rminus; apply Rplus_le_compat.
               apply Rle_trans with(r2:=x+h); tauto.
               apply Ropp_le_contravar; tauto.
               apply Rge_minus; apply Rle_ge; tauto.
               unfold In in H3, H4; unfold cc in H3, H4.
               destruct H3, H4.
               split.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; auto.
               rewrite Rabs_right; auto.
               apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
               rewrite Rplus_comm.
               apply Rle_trans with(r2:=x+h).
               apply Rplus_le_compat_r; tauto. tauto.
               apply Rgt_ge; auto.
               unfold In in H8; unfold cc in H8; destruct H8.
               rewrite Rabs_right. rewrite Rabs_right.
               apply Rplus_le_reg_r with(r:=x).
               rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
               apply Rgt_ge; auto.
               apply Rge_minus; apply Rle_ge; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
Qed.