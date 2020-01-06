Require Export Reals.
Open Scope R_scope.

(* 定义：实数构成的集合 *)

Definition R_Ensemble := R -> Prop.

(* 定义：实数x属于集合A *)

Definition In (x:R)(A:R_Ensemble) :Prop := A x.

Notation "x ∈ A" := (In x A) (at level 10).

(* 定义：区间 *)
(* 通过check命令我们可以查看我们所定义的区间类型为R_Ensemble.
   例： Variable a b:R.
       Check oo a b. *)

(* 闭区间 *)
Definition oo (a b:R) := fun x:R => a<b/\a<x<b.
Notation "( a , b )" := (oo a b).

(* 闭区间 *)
Definition cc (a b:R) := fun x:R => a<b/\a<=x<=b.
Notation "[ a , b ]" := (cc a b).

(* 半开半闭区间-左开右闭 *)
Definition oc (a b:R) := fun x:R => a<b/\a<x<=b.
Notation "( a , b ]" := (oc a b).

(* 半开半闭区间-左闭右开 *)
Definition co (a b:R) := fun x:R => a<b/\a<=x<b.
Notation "[ a , b )" := (co a b).

(* 函数在区间上一些基本性质的形式化描述 *)

(* 函数f在区间q上单调增 *)
Definition mon_increasing f (q:R_Ensemble) :=
  forall x y:R, x ∈ q /\ y ∈ q /\ y-x>0 -> f x <= f y.

(* 函数f在区间q上严格单调增 *)
Definition strict_mon_increasing f (q:R_Ensemble) :=
  forall x y:R, x ∈ q /\ y ∈ q /\ y-x>0 -> f x < f y.

(* 函数f在区间q上单调减 *)
Definition mon_decreasing f (q:R_Ensemble) :=
  forall x y:R, x ∈ q /\ y ∈ q /\ y-x>0 -> f x >= f y.

(* 函数f在区间q上严格单调减 *)
Definition strict_mon_decreasing f (q:R_Ensemble) :=
  forall x y:R, x ∈ q /\ y ∈ q /\ y-x>0 -> f x > f y.

(* 函数f在区间q上倒数无界 *)
Definition bounded_rec_f f (q:R_Ensemble) :=
  forall M:R, M>0 -> exists z:R, z ∈ q /\ M < Rabs(1/(f z)).

(* 函数f在区间q上正值单调不减 *)
Definition pos_inc f (q:R_Ensemble) := 
  (forall z:R, z ∈ q -> f z > 0) /\
  (forall z1 z2:R, z1 ∈ q -> z2 ∈ q -> z1<z2 -> f z1 <= f z2).

(* 函数f在区间q上正值单调不增 *)
Definition pos_dec f (q:R_Ensemble) :=
  (forall z:R, z ∈ q -> f z > 0) /\
  (forall z1 z2:R, z1 ∈ q -> z2 ∈ q -> z1<z2 -> f z2 >= f z1).

(* 一些组合函数、复合函数的形式化描述 *)

(* 设有函数下面给出函数cf(x)的形式化描述 *)
Definition mult_real_f (c:R) f := fun x:R => (c * (f x)).

(* 设有函数f1(x)、f2(x)，下面给出函数f1(x)+f2(x)的形式化描述 *)
Definition plus_Fu f1 f2   := fun x:R => f1 x + f2 x.

(* 设有函数f(x)，实数c，下面给出函数f(cx)的形式化描述 *)
Definition Com_F_c (f:R->R) c x := f (c * x). 

(* 设有函数f(x)，实数c、d，下面给出函数f(cx+d)的形式化描述 *)
Definition Com_F (f:R->R) (c d x:R) := f (c*x+d).


(* 排中律 *)
Axiom classic : forall P : Prop, P \/ ~P.

Theorem not_and_or : forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros.
  generalize(classic P); intro.
  generalize(classic Q); intro.
  destruct H0. destruct H1.
  assert(P/\Q). { split; auto. }
  contradiction.
  right; auto. left; auto.
Qed.
