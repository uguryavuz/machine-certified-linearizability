(* automatically generated -- do not edit manually *)
theory POPL24_HerlihyWingQueuePrelude imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'77:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<Longrightarrow> (((IsFiniteSet ((((A) \<union> ({(s)})))))) \<Longrightarrow> (((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f), (m))), (fapply ((f), (n))))))))))))))))"
shows "(((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f), (m))), (fapply ((f), (n)))))))))))))"(is "PROP ?ob'77")
proof -
ML_command {* writeln "*** TLAPS ENTER 77"; *}
show "PROP ?ob'77"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_d6e210.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_d6e210.znn.out
;; obligation #77
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (=> (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z)) (=> (IsFiniteSet (TLA.cup A
(TLA.set s))) (=> (/\ (TLA.in (TLA.cup A (TLA.set s)) (TLA.SUBSET arith.Z))
(IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f m)
(TLA.fapply f n))))))))))))
$goal (=> (/\ (TLA.in (TLA.cup A (TLA.set s)) (TLA.SUBSET arith.Z))
(IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f m)
(TLA.fapply f n))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"(((A \\cup {s}) \\in SUBSET(Int))=>(IsFiniteSet((A \\cup {s}))=>((((A \\cup {s}) \\in SUBSET(Int))&IsFiniteSet((A \\cup {s})))=>bEx(Bijection(isa'dotdot(1, Cardinality((A \\cup {s}))), (A \\cup {s})), (\<lambda>f. bAll(isa'dotdot(1, Cardinality((A \\cup {s}))), (\<lambda>m. bAll(isa'dotdot(1, Cardinality((A \\cup {s}))), (\<lambda>n. ((m < n)=>((f[m]) < (f[n]))))))))))))" (is "?z_he=>?z_hl")
 using v'160 by blast
 assume z_Hd:"(~((?z_he&IsFiniteSet((A \\cup {s})))=>bEx(Bijection(isa'dotdot(1, Cardinality((A \\cup {s}))), (A \\cup {s})), (\<lambda>f. bAll(isa'dotdot(1, Cardinality((A \\cup {s}))), (\<lambda>m. bAll(isa'dotdot(1, Cardinality((A \\cup {s}))), (\<lambda>n. ((m < n)=>((f[m]) < (f[n])))))))))))" (is "~(?z_ho=>?z_hp)")
 have z_Ho: "?z_ho" (is "_&?z_hm")
 by (rule zenon_notimply_0 [OF z_Hd])
 have z_Hbh: "(~?z_hp)"
 by (rule zenon_notimply_1 [OF z_Hd])
 have z_He: "?z_he"
 by (rule zenon_and_0 [OF z_Ho])
 have z_Hm: "?z_hm"
 by (rule zenon_and_1 [OF z_Ho])
 show FALSE
 proof (rule zenon_imply [OF z_Hc])
  assume z_Hbi:"(~?z_he)"
  show FALSE
  by (rule notE [OF z_Hbi z_He])
 next
  assume z_Hl:"?z_hl" (is "_=>?z_hn")
  show FALSE
  proof (rule zenon_imply [OF z_Hl])
   assume z_Hbj:"(~?z_hm)"
   show FALSE
   by (rule notE [OF z_Hbj z_Hm])
  next
   assume z_Hn:"?z_hn"
   show FALSE
   proof (rule zenon_imply [OF z_Hn])
    assume z_Hbk:"(~?z_ho)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbk])
     assume z_Hbi:"(~?z_he)"
     show FALSE
     by (rule notE [OF z_Hbi z_He])
    next
     assume z_Hbj:"(~?z_hm)"
     show FALSE
     by (rule notE [OF z_Hbj z_Hm])
    qed
   next
    assume z_Hp:"?z_hp"
    show FALSE
    by (rule notE [OF z_Hbh z_Hp])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 77"; *} qed
lemma ob'72:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'177: "(((\<forall> y \<in> (A) : ((less ((y), (s))))) \<Longrightarrow> (((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))))"
assumes v'178: "(((\<forall> y \<in> (A) : ((less ((s), (y))))) \<Longrightarrow> (((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))))"
assumes v'179: "((((((~ (\<forall> y \<in> (A) : ((less ((y), (s))))))) \<and> ((~ (\<forall> y \<in> (A) : ((less ((s), (y))))))))) \<Longrightarrow> (((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))))"
shows "(((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))"(is "PROP ?ob'72")
proof -
ML_command {* writeln "*** TLAPS ENTER 72"; *}
show "PROP ?ob'72"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_83d6df.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_83d6df.znn.out
;; obligation #72
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) A))
$hyp "v'177" (=> (TLA.bAll A ((y) (arith.lt y s))) (=> (/\ (TLA.in (TLA.cup A
(TLA.set s)) (TLA.SUBSET arith.Z)) (IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n)))))))))))
$hyp "v'178" (=> (TLA.bAll A ((y) (arith.lt s y))) (=> (/\ (TLA.in (TLA.cup A
(TLA.set s)) (TLA.SUBSET arith.Z)) (IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n)))))))))))
$hyp "v'179" (=> (/\ (-. (TLA.bAll A ((y) (arith.lt y s))))
(-. (TLA.bAll A ((y) (arith.lt s y))))) (=> (/\ (TLA.in (TLA.cup A
(TLA.set s)) (TLA.SUBSET arith.Z)) (IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n)))))))))))
$goal (=> (/\ (TLA.in (TLA.cup A (TLA.set s)) (TLA.SUBSET arith.Z))
(IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"(bAll(A, (\<lambda>y. (y < s)))=>((((A \\cup {s}) \\in SUBSET(Int))&IsFiniteSet((A \\cup {s})))=>bEx(Bijection(isa'dotdot(1, Cardinality((A \\cup {s}))), (A \\cup {s})), (\<lambda>f_1. bAll(isa'dotdot(1, Cardinality((A \\cup {s}))), (\<lambda>m. bAll(isa'dotdot(1, Cardinality((A \\cup {s}))), (\<lambda>n. ((m < n)=>((f_1[m]) < (f_1[n])))))))))))" (is "?z_hj=>?z_hp")
 using v'177 by blast
 have z_Hh:"(((~?z_hj)&(~bAll(A, (\<lambda>y. (s < y)))))=>?z_hp)" (is "?z_hbn=>_")
 using v'179 by blast
 have z_Hg:"(bAll(A, (\<lambda>y. (s < y)))=>?z_hp)" (is "?z_hbq=>_")
 using v'178 by blast
 assume z_Hi:"(~?z_hp)" (is "~(?z_hq=>?z_hv)")
 have z_Hq: "?z_hq" (is "?z_hc&?z_hd")
 by (rule zenon_notimply_0 [OF z_Hi])
 have z_Hbt: "(~?z_hv)"
 by (rule zenon_notimply_1 [OF z_Hi])
 have z_Hc: "?z_hc"
 by (rule zenon_and_0 [OF z_Hq])
 have z_Hd: "?z_hd"
 by (rule zenon_and_1 [OF z_Hq])
 show FALSE
 proof (rule zenon_imply [OF z_Hf])
  assume z_Hbo:"(~?z_hj)"
  show FALSE
  proof (rule zenon_imply [OF z_Hg])
   assume z_Hbp:"(~?z_hbq)"
   show FALSE
   proof (rule zenon_imply [OF z_Hh])
    assume z_Hbu:"(~?z_hbn)" (is "~(?z_hbo&?z_hbp)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbu])
     assume z_Hbv:"(~?z_hbo)"
     show FALSE
     by (rule notE [OF z_Hbv z_Hbo])
    next
     assume z_Hbw:"(~?z_hbp)"
     show FALSE
     by (rule notE [OF z_Hbw z_Hbp])
    qed
   next
    assume z_Hp:"?z_hp"
    show FALSE
    proof (rule zenon_imply [OF z_Hp])
     assume z_Hbx:"(~?z_hq)"
     show FALSE
     proof (rule zenon_notand [OF z_Hbx])
      assume z_Hby:"(~?z_hc)"
      show FALSE
      by (rule notE [OF z_Hby z_Hc])
     next
      assume z_Hbz:"(~?z_hd)"
      show FALSE
      by (rule notE [OF z_Hbz z_Hd])
     qed
    next
     assume z_Hv:"?z_hv"
     show FALSE
     by (rule notE [OF z_Hbt z_Hv])
    qed
   qed
  next
   assume z_Hp:"?z_hp"
   show FALSE
   proof (rule zenon_imply [OF z_Hp])
    assume z_Hbx:"(~?z_hq)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbx])
     assume z_Hby:"(~?z_hc)"
     show FALSE
     by (rule notE [OF z_Hby z_Hc])
    next
     assume z_Hbz:"(~?z_hd)"
     show FALSE
     by (rule notE [OF z_Hbz z_Hd])
    qed
   next
    assume z_Hv:"?z_hv"
    show FALSE
    by (rule notE [OF z_Hbt z_Hv])
   qed
  qed
 next
  assume z_Hp:"?z_hp"
  show FALSE
  proof (rule zenon_imply [OF z_Hp])
   assume z_Hbx:"(~?z_hq)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbx])
    assume z_Hby:"(~?z_hc)"
    show FALSE
    by (rule notE [OF z_Hby z_Hc])
   next
    assume z_Hbz:"(~?z_hd)"
    show FALSE
    by (rule notE [OF z_Hbz z_Hd])
   qed
  next
   assume z_Hv:"?z_hv"
   show FALSE
   by (rule notE [OF z_Hbt z_Hv])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 72"; *} qed
lemma ob'63:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
assumes v'156: "(((((((S) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((S)))))) \<Rightarrow> (\<exists> f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))), (S)))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f), (m))), (fapply ((f), (n)))))))))))))"
shows "(\<exists> f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))), (S)))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f), (m))), (fapply ((f), (n)))))))))))"(is "PROP ?ob'63")
proof -
ML_command {* writeln "*** TLAPS ENTER 63"; *}
show "PROP ?ob'63"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_dc6cfb.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_dc6cfb.znn.out
;; obligation #63
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'156" (=> (/\ (TLA.in S (TLA.SUBSET arith.Z)) (IsFiniteSet S))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (Cardinality S))
S) ((f) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) ((n) (=> (arith.lt m n) (arith.lt (TLA.fapply f m)
(TLA.fapply f n))))))))))
$goal (TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) S) ((f) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) ((n) (=> (arith.lt m n) (arith.lt (TLA.fapply f m)
(TLA.fapply f n)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"(((S \\in SUBSET(Int))&IsFiniteSet(S))=>bEx(Bijection(isa'dotdot(1, Cardinality(S)), S), (\<lambda>f. bAll(isa'dotdot(1, Cardinality(S)), (\<lambda>m. bAll(isa'dotdot(1, Cardinality(S)), (\<lambda>n. ((m < n)=>((f[m]) < (f[n]))))))))))" (is "?z_he=>?z_hi")
 using v'156 by blast
 have z_Hb:"IsFiniteSet(S)" (is "?z_hb")
 using v'150 by blast
 have z_Ha:"(S \\in SUBSET(Int))" (is "?z_ha")
 using S_in by blast
 assume z_Hd:"(~?z_hi)"
 show FALSE
 proof (rule zenon_imply [OF z_Hc])
  assume z_Hba:"(~?z_he)"
  show FALSE
  proof (rule zenon_notand [OF z_Hba])
   assume z_Hbb:"(~?z_ha)"
   show FALSE
   by (rule notE [OF z_Hbb z_Ha])
  next
   assume z_Hbc:"(~?z_hb)"
   show FALSE
   by (rule notE [OF z_Hbc z_Hb])
  qed
 next
  assume z_Hi:"?z_hi"
  show FALSE
  by (rule notE [OF z_Hd z_Hi])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 63"; *} qed
lemma ob'58:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'149: "(((S) \<noteq> ({})))"
assumes v'150: "((IsFiniteSet ((S))))"
(* usable definition P suppressed *)
assumes v'158: "((P (({}))))"
assumes v'159: "((\<And> A :: c. (\<And> s :: c. (((P ((A)))) \<Longrightarrow> ((((s) \<notin> (A))) \<Longrightarrow> ((P ((((A) \<union> ({(s)})))))))))))"
assumes v'160: "((\<And> S_1 :: c. (((IsFiniteSet ((S_1)))) \<Longrightarrow> (\<And> P_1 :: c => c. (((P_1 (({})))) \<Longrightarrow> (((\<And> T :: c. (\<And> x :: c. (((IsFiniteSet ((T)))) \<Longrightarrow> (((P_1 ((T)))) \<Longrightarrow> ((((x) \<notin> (T))) \<Longrightarrow> ((P_1 ((((T) \<union> ({(x)})))))))))))) \<Longrightarrow> ((P_1 ((S_1))))))))))"
shows "((P ((S))))"(is "PROP ?ob'58")
proof -
ML_command {* writeln "*** TLAPS ENTER 58"; *}
show "PROP ?ob'58"
using assms by blast
ML_command {* writeln "*** TLAPS EXIT 58"; *} qed
lemma ob'33:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'149: "(((S) \<noteq> ({})))"
assumes v'150: "((IsFiniteSet ((S))))"
assumes v'156: "(((((((((S) \<in> ((SUBSET (Int))))) \<and> (((S) \<noteq> ({}))))) \<and> ((IsFiniteSet ((S)))))) \<Rightarrow> (\<exists> s \<in> (S) : (\<forall> y \<in> (S) : ((leq ((y), (s))))))))"
shows "(\<exists> s \<in> (S) : (\<forall> y \<in> (S) : ((leq ((y), (s))))))"(is "PROP ?ob'33")
proof -
ML_command {* writeln "*** TLAPS ENTER 33"; *}
show "PROP ?ob'33"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_a40401.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_a40401.znn.out
;; obligation #33
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'149" (-. (= S
TLA.emptyset))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'156" (=> (/\ (/\ (TLA.in S (TLA.SUBSET arith.Z)) (-. (= S
TLA.emptyset))) (IsFiniteSet S)) (TLA.bEx S ((s) (TLA.bAll S ((y) (arith.le y
s))))))
$goal (TLA.bEx S ((s) (TLA.bAll S ((y) (arith.le y
s)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"((((S \\in SUBSET(Int))&(S~={}))&IsFiniteSet(S))=>bEx(S, (\<lambda>s. bAll(S, (\<lambda>y. (y <= s))))))" (is "?z_hf=>?z_hl")
 using v'156 by blast
 have z_Hc:"IsFiniteSet(S)" (is "?z_hc")
 using v'150 by blast
 have z_Ha:"(S \\in SUBSET(Int))" (is "?z_ha")
 using S_in by blast
 have z_Hb:"(S~={})"
 using v'149 by blast
 assume z_He:"(~?z_hl)"
 show FALSE
 proof (rule zenon_imply [OF z_Hd])
  assume z_Hs:"(~?z_hf)" (is "~(?z_hg&_)")
  show FALSE
  proof (rule zenon_notand [OF z_Hs])
   assume z_Ht:"(~?z_hg)" (is "~(_&?z_hb)")
   show FALSE
   proof (rule zenon_notand [OF z_Ht])
    assume z_Hu:"(~?z_ha)"
    show FALSE
    by (rule notE [OF z_Hu z_Ha])
   next
    assume z_Hv:"(~?z_hb)" (is "~~?z_hw")
    show FALSE
    by (rule notE [OF z_Hv z_Hb])
   qed
  next
   assume z_Hx:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hx z_Hc])
  qed
 next
  assume z_Hl:"?z_hl"
  show FALSE
  by (rule notE [OF z_He z_Hl])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 33"; *} qed
lemma ob'22:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes v'148: "((IsFiniteSet ((S))))"
fixes pi
assumes pi_in : "(pi \<in> ((Perm ((S)))))"
fixes k
assumes k_in : "(k \<in> ((DOMAIN (pi))))"
fixes m
assumes m_in : "(m \<in> ((DOMAIN (pi))))"
assumes v'152: "(((k) \<noteq> (m)))"
assumes v'153: "(((fapply ((pi), (k))) = (fapply ((pi), (m)))))"
assumes v'163: "((IsFiniteSet (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))))))"
assumes v'164: "(((m) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S)))))))))"
assumes v'165: "((((Cardinality (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S)))))))))) = ((Cardinality ((S))))))"
assumes v'166: "((\<And> S_1 :: c. (\<And> x :: c. (((IsFiniteSet ((S_1)))) \<Longrightarrow> (((IsFiniteSet ((((S_1) \\ ({(x)})))))) & ((((Cardinality ((((S_1) \\ ({(x)})))))) = (cond((((x) \<in> (S_1))), ((arith_add (((Cardinality ((S_1)))), ((minus (((Succ[0])))))))), ((Cardinality ((S_1)))))))))))))"
shows "((((Cardinality (((((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \\ ({(m)})))))) = ((arith_add (((Cardinality ((S)))), ((minus (((Succ[0]))))))))))"(is "PROP ?ob'22")
proof -
ML_command {* writeln "*** TLAPS ENTER 22"; *}
show "PROP ?ob'22"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_4976ee.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_4976ee.znn.out
;; obligation #22
$hyp "v'148" (IsFiniteSet S)
$hyp "pi_in" (TLA.in pi (Perm S))
$hyp "k_in" (TLA.in k (TLA.DOMAIN pi))
$hyp "m_in" (TLA.in m (TLA.DOMAIN pi))
$hyp "v'152" (-. (= k m))
$hyp "v'153" (= (TLA.fapply pi k)
(TLA.fapply pi m))
$hyp "v'163" (IsFiniteSet (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)))
$hyp "v'164" (TLA.in m (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)))
$hyp "v'165" (= (Cardinality (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)))
(Cardinality S))
$hyp "v'166" (A. ((S_1) (A. ((x) (=> (IsFiniteSet S_1) (/\ (IsFiniteSet (TLA.setminus S_1
(TLA.set x))) (= (Cardinality (TLA.setminus S_1 (TLA.set x)))
(TLA.cond (TLA.in x S_1) (arith.add (Cardinality S_1)
(arith.minus (TLA.fapply TLA.Succ 0))) (Cardinality S_1)))))))))
$goal (= (Cardinality (TLA.setminus (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) (TLA.set m))) (arith.add (Cardinality S)
(arith.minus (TLA.fapply TLA.Succ 0))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"(\\A S_1:(\\A x:(IsFiniteSet(S_1)=>(IsFiniteSet((S_1 \\ {x}))&(Cardinality((S_1 \\ {x}))=cond((x \\in S_1), (Cardinality(S_1) +  -.(1)), Cardinality(S_1)))))))" (is "\\A x : ?z_hbc(x)")
 using v'166 by blast
 have z_Hh:"(m \\in isa'dotdot(1, Cardinality(S)))" (is "?z_hh")
 using v'164 by blast
 have z_Hi:"(Cardinality(isa'dotdot(1, Cardinality(S)))=Cardinality(S))" (is "?z_hbh=?z_hbf")
 using v'165 by blast
 have z_Hg:"IsFiniteSet(isa'dotdot(1, ?z_hbf))" (is "?z_hg")
 using v'163 by blast
 assume z_Hk:"(Cardinality((isa'dotdot(1, ?z_hbf) \\ {m}))~=(?z_hbf +  -.(1)))" (is "?z_hbi~=?z_hbl")
 have z_Hbm: "?z_hbc(isa'dotdot(1, ?z_hbf))" (is "\\A x : ?z_hbn(x)")
 by (rule zenon_all_0 [of "?z_hbc" "isa'dotdot(1, ?z_hbf)", OF z_Hj])
 have z_Hbo: "?z_hbn(m)" (is "_=>?z_hbp")
 by (rule zenon_all_0 [of "?z_hbn" "m", OF z_Hbm])
 show FALSE
 proof (rule zenon_imply [OF z_Hbo])
  assume z_Hbq:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hbq z_Hg])
 next
  assume z_Hbp:"?z_hbp" (is "?z_hbr&?z_hbs")
  have z_Hbs: "?z_hbs" (is "_=?z_hbt")
  by (rule zenon_and_1 [OF z_Hbp])
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vej. (?z_hbi=zenon_Vej))" "?z_hh" "(?z_hbh +  -.(1))" "?z_hbh", OF z_Hbs])
   assume z_Hh:"?z_hh"
   assume z_Hby:"(?z_hbi=(?z_hbh +  -.(1)))" (is "_=?z_hbx")
   show FALSE
   proof (rule notE [OF z_Hk])
    have z_Hbz: "(?z_hbx=?z_hbl)"
    proof (rule zenon_nnpp [of "(?z_hbx=?z_hbl)"])
     assume z_Hca:"(?z_hbx~=?z_hbl)"
     show FALSE
     proof (rule zenon_noteq [of "?z_hbl"])
      have z_Hcb: "(?z_hbl~=?z_hbl)"
      by (rule subst [where P="(\<lambda>zenon_Vbl. ((zenon_Vbl +  -.(1))~=?z_hbl))", OF z_Hi], fact z_Hca)
      thus "(?z_hbl~=?z_hbl)" .
     qed
    qed
    have z_Hcg: "(?z_hbi=?z_hbl)"
    by (rule subst [where P="(\<lambda>zenon_Vej. (?z_hbi=zenon_Vej))", OF z_Hbz], fact z_Hby)
    thus "(?z_hbi=?z_hbl)" .
   qed
  next
   assume z_Hch:"(~?z_hh)"
   assume z_Hci:"(?z_hbi=?z_hbh)"
   show FALSE
   by (rule notE [OF z_Hch z_Hh])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 22"; *} qed
lemma ob'14:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes v'148: "((IsFiniteSet ((S))))"
fixes pi
assumes pi_in : "(pi \<in> ((Perm ((S)))))"
fixes k
assumes k_in : "(k \<in> ((DOMAIN (pi))))"
fixes m
assumes m_in : "(m \<in> ((DOMAIN (pi))))"
assumes v'152: "(((k) \<noteq> (m)))"
assumes v'153: "(((fapply ((pi), (k))) = (fapply ((pi), (m)))))"
assumes v'160: "((IsFiniteSet (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))))))"
assumes v'161: "((\<And> S_1 :: c. (\<And> x :: c. (((IsFiniteSet ((S_1)))) \<Longrightarrow> (((IsFiniteSet ((((S_1) \\ ({(x)})))))) & ((((Cardinality ((((S_1) \\ ({(x)})))))) = (cond((((x) \<in> (S_1))), ((arith_add (((Cardinality ((S_1)))), ((minus (((Succ[0])))))))), ((Cardinality ((S_1)))))))))))))"
shows "((IsFiniteSet (((((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \\ ({(m)}))))))"(is "PROP ?ob'14")
proof -
ML_command {* writeln "*** TLAPS ENTER 14"; *}
show "PROP ?ob'14"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_b9cfeb.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_b9cfeb.znn.out
;; obligation #14
$hyp "v'148" (IsFiniteSet S)
$hyp "pi_in" (TLA.in pi (Perm S))
$hyp "k_in" (TLA.in k (TLA.DOMAIN pi))
$hyp "m_in" (TLA.in m (TLA.DOMAIN pi))
$hyp "v'152" (-. (= k m))
$hyp "v'153" (= (TLA.fapply pi k)
(TLA.fapply pi m))
$hyp "v'160" (IsFiniteSet (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)))
$hyp "v'161" (A. ((S_1) (A. ((x) (=> (IsFiniteSet S_1) (/\ (IsFiniteSet (TLA.setminus S_1
(TLA.set x))) (= (Cardinality (TLA.setminus S_1 (TLA.set x)))
(TLA.cond (TLA.in x S_1) (arith.add (Cardinality S_1)
(arith.minus (TLA.fapply TLA.Succ 0))) (Cardinality S_1)))))))))
$goal (IsFiniteSet (TLA.setminus (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S))
(TLA.set m)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A S_1:(\\A x:(IsFiniteSet(S_1)=>(IsFiniteSet((S_1 \\ {x}))&(Cardinality((S_1 \\ {x}))=cond((x \\in S_1), (Cardinality(S_1) +  -.(1)), Cardinality(S_1)))))))" (is "\\A x : ?z_hba(x)")
 using v'161 by blast
 have z_Hg:"IsFiniteSet(isa'dotdot(1, Cardinality(S)))" (is "?z_hg")
 using v'160 by blast
 assume z_Hi:"(~IsFiniteSet((isa'dotdot(1, Cardinality(S)) \\ {m})))" (is "~?z_hbe")
 have z_Hbi: "?z_hba(isa'dotdot(1, Cardinality(S)))" (is "\\A x : ?z_hbj(x)")
 by (rule zenon_all_0 [of "?z_hba" "isa'dotdot(1, Cardinality(S))", OF z_Hh])
 have z_Hbk: "?z_hbj(m)" (is "_=>?z_hbl")
 by (rule zenon_all_0 [of "?z_hbj" "m", OF z_Hbi])
 show FALSE
 proof (rule zenon_imply [OF z_Hbk])
  assume z_Hbm:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hbm z_Hg])
 next
  assume z_Hbl:"?z_hbl" (is "_&?z_hbn")
  have z_Hbe: "?z_hbe"
  by (rule zenon_and_0 [OF z_Hbl])
  show FALSE
  by (rule notE [OF z_Hi z_Hbe])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 14"; *} qed
lemma ob'8:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes v'147: "((IsFiniteSet ((S))))"
fixes pi
assumes pi_in : "(pi \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \<rightarrow> (S)]), %f. (\<forall> w \<in> (S) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (((fapply ((f), (q))) = (w))))))))"
fixes k
assumes k_in : "(k \<in> ((DOMAIN (pi))))"
fixes m
assumes m_in : "(m \<in> ((DOMAIN (pi))))"
assumes v'151: "(((k) \<noteq> (m)))"
assumes v'152: "(((fapply ((pi), (k))) = (fapply ((pi), (m)))))"
assumes v'157: "((\<And> S_1 :: c. (\<And> T :: c. (\<And> F :: c. F \<in> ([(S_1) \<rightarrow> (T)]) \<Longrightarrow> ((\<forall> t \<in> (T) : (\<exists> s \<in> (S_1) : (((fapply ((F), (s))) = (t))))) \<Longrightarrow> (((F) \<in> ((Surjection ((S_1), (T)))))))))))"
shows "((([ s \<in> ((((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \\ ({(m)})))  \<mapsto> (fapply ((pi), (s)))]) \<in> ((Surjection (((((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \\ ({(m)}))), (S))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_648328.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_648328.znn.out
;; obligation #8
$hyp "v'147" (IsFiniteSet S)
$hyp "pi_in" (TLA.in pi (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) S) ((f) (TLA.bAll S ((w) (TLA.bEx (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) ((q) (= (TLA.fapply f q)
w))))))))
$hyp "k_in" (TLA.in k (TLA.DOMAIN pi))
$hyp "m_in" (TLA.in m (TLA.DOMAIN pi))
$hyp "v'151" (-. (= k m))
$hyp "v'152" (= (TLA.fapply pi k)
(TLA.fapply pi m))
$hyp "v'157" (A. ((S_1) (A. ((T) (TLA.bAll (TLA.FuncSet S_1 T) ((F) (=> (TLA.bAll T ((t) (TLA.bEx S_1 ((s) (= (TLA.fapply F s)
t))))) (TLA.in F (Surjection S_1
T)))))))))
$goal (TLA.in (TLA.Fcn (TLA.setminus (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) (TLA.set m)) ((s) (TLA.fapply pi s)))
(Surjection (TLA.setminus (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality S)) (TLA.set m))
S))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"(pi \\in subsetOf(FuncSet(isa'dotdot(1, Cardinality(S)), S), (\<lambda>f. bAll(S, (\<lambda>w. bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((f[q])=w))))))))" (is "?z_hb")
 using pi_in by blast
 have z_He:"(k~=m)"
 using v'151 by blast
 have z_Hc:"(k \\in DOMAIN(pi))" (is "?z_hc")
 using k_in by blast
 have z_Hf:"((pi[k])=(pi[m]))" (is "?z_hbc=?z_hbd")
 using v'152 by blast
 have z_Hg:"(\\A S_1:(\\A T:bAll(FuncSet(S_1, T), (\<lambda>F. (bAll(T, (\<lambda>t. bEx(S_1, (\<lambda>s. ((F[s])=t)))))=>(F \\in Surjection(S_1, T)))))))" (is "\\A x : ?z_hbw(x)")
 using v'157 by blast
 have zenon_L1_: "(k \\in {m}) ==> (k~=m) ==> FALSE" (is "?z_hbx ==> ?z_he ==> FALSE")
 proof -
  assume z_Hbx:"?z_hbx"
  assume z_He:"?z_he"
  show FALSE
  proof (rule zenon_in_addElt [of "k" "m" "{}", OF z_Hbx])
   assume z_Hca:"(k=m)"
   show FALSE
   by (rule notE [OF z_He z_Hca])
  next
   assume z_Hcb:"(k \\in {})" (is "?z_hcb")
   show FALSE
   by (rule zenon_in_emptyset [of "k", OF z_Hcb])
  qed
 qed
 have zenon_L2_: "(~(k \\in (isa'dotdot(1, Cardinality(S)) \\ {m}))) ==> (k~=m) ==> ?z_hc ==> (DOMAIN(pi)=isa'dotdot(1, Cardinality(S))) ==> FALSE" (is "?z_hcc ==> ?z_he ==> _ ==> ?z_hcf ==> FALSE")
 proof -
  assume z_Hcc:"?z_hcc" (is "~?z_hcd")
  assume z_He:"?z_he"
  assume z_Hc:"?z_hc"
  assume z_Hcf:"?z_hcf" (is "?z_hbb=?z_hl")
  show FALSE
  proof (rule zenon_notin_setminus [of "k" "?z_hl" "{m}", OF z_Hcc])
   assume z_Hcg:"(~(k \\in ?z_hl))" (is "~?z_hch")
   have z_Hci: "(\\A zenon_Vha:((zenon_Vha \\in ?z_hbb)<=>(zenon_Vha \\in ?z_hl)))" (is "\\A x : ?z_hcn(x)")
   by (rule zenon_setequal_0 [of "?z_hbb" "?z_hl", OF z_Hcf])
   have z_Hco: "?z_hcn(k)"
   by (rule zenon_all_0 [of "?z_hcn" "k", OF z_Hci])
   show FALSE
   proof (rule zenon_equiv [OF z_Hco])
    assume z_Hcp:"(~?z_hc)"
    assume z_Hcg:"(~?z_hch)"
    show FALSE
    by (rule notE [OF z_Hcp z_Hc])
   next
    assume z_Hc:"?z_hc"
    assume z_Hch:"?z_hch"
    show FALSE
    by (rule notE [OF z_Hcg z_Hch])
   qed
  next
   assume z_Hbx:"(k \\in {m})" (is "?z_hbx")
   show FALSE
   by (rule zenon_L1_ [OF z_Hbx z_He])
  qed
 qed
 have zenon_L3_: "(~((CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))))) \\in (isa'dotdot(1, Cardinality(S)) \\ {m}))) ==> (m~=(CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))))) ==> ((CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))))) \\in isa'dotdot(1, Cardinality(S))) ==> FALSE" (is "?z_hcq ==> ?z_hdj ==> ?z_hdk ==> FALSE")
 proof -
  assume z_Hcq:"?z_hcq" (is "~?z_hcr")
  assume z_Hdj:"?z_hdj" (is "_~=?z_hcs")
  assume z_Hdk:"?z_hdk"
  show FALSE
  proof (rule zenon_notin_setminus [of "?z_hcs" "isa'dotdot(1, Cardinality(S))" "{m}", OF z_Hcq])
   assume z_Hdl:"(~?z_hdk)"
   show FALSE
   by (rule notE [OF z_Hdl z_Hdk])
  next
   assume z_Hdm:"(?z_hcs \\in {m})" (is "?z_hdm")
   show FALSE
   proof (rule zenon_in_addElt [of "?z_hcs" "m" "{}", OF z_Hdm])
    assume z_Hdn:"(?z_hcs=m)"
    show FALSE
    by (rule zenon_eqsym [OF z_Hdn z_Hdj])
   next
    assume z_Hdo:"(?z_hcs \\in {})" (is "?z_hdo")
    show FALSE
    by (rule zenon_in_emptyset [of "?z_hcs", OF z_Hdo])
   qed
  qed
 qed
 have zenon_L4_: "(((CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))))) \\in isa'dotdot(1, Cardinality(S)))&((pi[(CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))))])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))) ==> (~(\\E x:((x \\in (isa'dotdot(1, Cardinality(S)) \\ {m}))&((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))))) ==> (?z_hbd~=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))) ==> FALSE" (is "?z_hdp ==> ?z_hds ==> ?z_hdy ==> FALSE")
 proof -
  assume z_Hdp:"?z_hdp" (is "?z_hdk&?z_hdq")
  assume z_Hds:"?z_hds" (is "~(\\E x : ?z_hdz(x))")
  assume z_Hdy:"?z_hdy" (is "_~=?z_hcy")
  have z_Hdk: "?z_hdk"
  by (rule zenon_and_0 [OF z_Hdp])
  have z_Hdq: "?z_hdq" (is "?z_hdr=_")
  by (rule zenon_and_1 [OF z_Hdp])
  show FALSE
  proof (rule notE [OF z_Hdy])
   have z_Hea: "(?z_hdr=?z_hbd)"
   proof (rule zenon_nnpp [of "(?z_hdr=?z_hbd)"])
    assume z_Heb:"(?z_hdr~=?z_hbd)"
    show FALSE
    proof (rule zenon_em [of "(?z_hbd=?z_hbd)"])
     assume z_Hec:"(?z_hbd=?z_hbd)"
     show FALSE
     proof (rule notE [OF z_Heb])
      have z_Hed: "(?z_hbd=?z_hdr)"
      proof (rule zenon_nnpp [of "(?z_hbd=?z_hdr)"])
       assume z_Hee:"(?z_hbd~=?z_hdr)"
       show FALSE
       proof (rule zenon_noteq [of "?z_hdr"])
        have z_Hef: "(m=(CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=?z_hcy))))" (is "_=?z_hcs")
        proof (rule zenon_nnpp [of "(m=?z_hcs)"])
         assume z_Hdj:"(m~=?z_hcs)"
         have z_Heg: "~?z_hdz(?z_hcs)" (is "~(?z_hcr&?z_heh)")
         by (rule zenon_notex_0 [of "?z_hdz" "?z_hcs", OF z_Hds])
         show FALSE
         proof (rule zenon_notand [OF z_Heg])
          assume z_Hcq:"(~?z_hcr)"
          show FALSE
          by (rule zenon_L3_ [OF z_Hcq z_Hdj z_Hdk])
         next
          assume z_Hei:"((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[?z_hcs])~=?z_hcy)" (is "?z_hej~=_")
          show FALSE
          proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vdc. (zenon_Vdc~=?z_hcy))" "(isa'dotdot(1, Cardinality(S)) \\ {m})" "(\<lambda>s. (pi[s]))" "?z_hcs", OF z_Hei])
           assume z_Hcq:"(~?z_hcr)"
           show FALSE
           by (rule zenon_L3_ [OF z_Hcq z_Hdj z_Hdk])
          next
           assume z_Hen:"(?z_hdr~=?z_hcy)"
           show FALSE
           by (rule notE [OF z_Hen z_Hdq])
          qed
         qed
        qed
        have z_Heo: "(?z_hdr~=?z_hdr)"
        by (rule subst [where P="(\<lambda>zenon_Vbd. ((pi[zenon_Vbd])~=?z_hdr))", OF z_Hef], fact z_Hee)
        thus "(?z_hdr~=?z_hdr)" .
       qed
      qed
      have z_Hea: "(?z_hdr=?z_hbd)"
      by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi=?z_hbd))", OF z_Hed], fact z_Hec)
      thus "(?z_hdr=?z_hbd)" .
     qed
    next
     assume z_Hew:"(?z_hbd~=?z_hbd)"
     show FALSE
     by (rule zenon_noteq [OF z_Hew])
    qed
   qed
   have z_Hex: "(?z_hbd=?z_hcy)"
   by (rule subst [where P="(\<lambda>zenon_Voc. (zenon_Voc=?z_hcy))", OF z_Hea], fact z_Hdq)
   thus "(?z_hbd=?z_hcy)" .
  qed
 qed
 have zenon_L5_: "(\\A x:((x \\in S)=>bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((pi[q])=x))))) ==> ((CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))) \\in S) ==> (~(\\E x:((x \\in (isa'dotdot(1, Cardinality(S)) \\ {m}))&((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))))) ==> (?z_hbd~=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))) ==> FALSE" (is "?z_hfb ==> ?z_hfh ==> ?z_hds ==> ?z_hdy ==> FALSE")
 proof -
  assume z_Hfb:"?z_hfb" (is "\\A x : ?z_hfi(x)")
  assume z_Hfh:"?z_hfh"
  assume z_Hds:"?z_hds" (is "~(\\E x : ?z_hdz(x))")
  assume z_Hdy:"?z_hdy" (is "_~=?z_hcy")
  have z_Hfj: "?z_hfi(?z_hcy)" (is "_=>?z_hfk")
  by (rule zenon_all_0 [of "?z_hfi" "?z_hcy", OF z_Hfb])
  show FALSE
  proof (rule zenon_imply [OF z_Hfj])
   assume z_Hfl:"(~?z_hfh)"
   show FALSE
   by (rule notE [OF z_Hfl z_Hfh])
  next
   assume z_Hfk:"?z_hfk"
   have z_Hfm_z_Hfk: "(\\E x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=?z_hcy))) == ?z_hfk" (is "?z_hfm == _")
   by (unfold bEx_def)
   have z_Hfm: "?z_hfm" (is "\\E x : ?z_hfn(x)")
   by (unfold z_Hfm_z_Hfk, fact z_Hfk)
   have z_Hdp: "?z_hfn((CHOOSE x:((x \\in isa'dotdot(1, Cardinality(S)))&((pi[x])=?z_hcy))))" (is "?z_hdk&?z_hdq")
   by (rule zenon_ex_choose_0 [of "?z_hfn", OF z_Hfm])
   show FALSE
   by (rule zenon_L4_ [OF z_Hdp z_Hds z_Hdy])
  qed
 qed
 have zenon_L6_: "(?z_hbc~=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))) ==> (?z_hbc=?z_hbd) ==> (\\A x:((x \\in S)=>bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((pi[q])=x))))) ==> ((CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))) \\in S) ==> (~(\\E x:((x \\in (isa'dotdot(1, Cardinality(S)) \\ {m}))&((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[x])=(CHOOSE x:(~((x \\in S)=>bEx((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. ((Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))))) ==> FALSE" (is "?z_hfo ==> ?z_hf ==> ?z_hfb ==> ?z_hfh ==> ?z_hds ==> FALSE")
 proof -
  assume z_Hfo:"?z_hfo" (is "_~=?z_hcy")
  assume z_Hf:"?z_hf"
  assume z_Hfb:"?z_hfb" (is "\\A x : ?z_hfi(x)")
  assume z_Hfh:"?z_hfh"
  assume z_Hds:"?z_hds" (is "~(\\E x : ?z_hdz(x))")
  show FALSE
  proof (rule notE [OF z_Hfo])
   have z_Hex: "(?z_hbd=?z_hcy)"
   proof (rule zenon_nnpp [of "(?z_hbd=?z_hcy)"])
    assume z_Hdy:"(?z_hbd~=?z_hcy)"
    show FALSE
    by (rule zenon_L5_ [OF z_Hfb z_Hfh z_Hds z_Hdy])
   qed
   have z_Hfp: "(?z_hbc=?z_hcy)"
   by (rule subst [where P="(\<lambda>zenon_Vi. (?z_hbc=zenon_Vi))", OF z_Hex], fact z_Hf)
   thus "(?z_hbc=?z_hcy)" .
  qed
 qed
 assume z_Hh:"(~(Fcn((isa'dotdot(1, Cardinality(S)) \\ {m}), (\<lambda>s. (pi[s]))) \\in Surjection((isa'dotdot(1, Cardinality(S)) \\ {m}), S)))" (is "~?z_hfs")
 have z_Hfu: "(pi \\in FuncSet(isa'dotdot(1, Cardinality(S)), S))" (is "?z_hfu")
 by (rule zenon_in_subsetof_0 [of "pi" "FuncSet(isa'dotdot(1, Cardinality(S)), S)" "(\<lambda>f. bAll(S, (\<lambda>w. bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((f[q])=w))))))", OF z_Hb])
 have z_Hfv: "bAll(S, (\<lambda>w. bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((pi[q])=w)))))" (is "?z_hfv")
 by (rule zenon_in_subsetof_1 [of "pi" "FuncSet(isa'dotdot(1, Cardinality(S)), S)" "(\<lambda>f. bAll(S, (\<lambda>w. bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((f[q])=w))))))", OF z_Hb])
 have z_Hfb_z_Hfv: "(\\A x:((x \\in S)=>bEx(isa'dotdot(1, Cardinality(S)), (\<lambda>q. ((pi[q])=x))))) == ?z_hfv" (is "?z_hfb == _")
 by (unfold bAll_def)
 have z_Hfb: "?z_hfb" (is "\\A x : ?z_hfi(x)")
 by (unfold z_Hfb_z_Hfv, fact z_Hfv)
 have z_Hcf: "(DOMAIN(pi)=isa'dotdot(1, Cardinality(S)))" (is "?z_hbb=?z_hl")
 by (rule zenon_in_funcset_1 [of "pi" "?z_hl" "S", OF z_Hfu])
 have z_Hga: "?z_hbw((?z_hl \\ {m}))" (is "\\A x : ?z_hgb(x)")
 by (rule zenon_all_0 [of "?z_hbw" "(?z_hl \\ {m})", OF z_Hg])
 have z_Hgc: "?z_hgb(S)" (is "?z_hgc")
 by (rule zenon_all_0 [of "?z_hgb" "S", OF z_Hga])
 have z_Hgd_z_Hgc: "(\\A x:((x \\in FuncSet((?z_hl \\ {m}), S))=>(bAll(S, (\<lambda>t. bEx((?z_hl \\ {m}), (\<lambda>s. ((x[s])=t)))))=>(x \\in Surjection((?z_hl \\ {m}), S))))) == ?z_hgc" (is "?z_hgd == _")
 by (unfold bAll_def)
 have z_Hgd: "?z_hgd" (is "\\A x : ?z_hgp(x)")
 by (unfold z_Hgd_z_Hgc, fact z_Hgc)
 have z_Hgq: "?z_hgp(Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s]))))" (is "?z_hgr=>?z_hgs")
 by (rule zenon_all_0 [of "?z_hgp" "Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))", OF z_Hgd])
 show FALSE
 proof (rule zenon_imply [OF z_Hgq])
  assume z_Hgt:"(~?z_hgr)"
  show FALSE
  proof (rule zenon_notin_funcset [of "Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))" "(?z_hl \\ {m})" "S", OF z_Hgt])
   assume z_Hgu:"(~isAFcn(Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))))" (is "~?z_hgv")
   show FALSE
   by (rule zenon_notisafcn_fcn [of "(?z_hl \\ {m})" "(\<lambda>s. (pi[s]))", OF z_Hgu])
  next
   assume z_Hgw:"(DOMAIN(Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s]))))~=(?z_hl \\ {m}))" (is "?z_hgx~=?z_hce")
   have z_Hgy: "(?z_hce~=?z_hce)"
   by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vab. (zenon_Vab~=?z_hce))" "?z_hce" "(\<lambda>s. (pi[s]))", OF z_Hgw])
   show FALSE
   by (rule zenon_noteq [OF z_Hgy])
  next
   assume z_Hhc:"(~(\\A zenon_Vto:((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S))))" (is "~(\\A x : ?z_hhj(x))")
   have z_Hhk: "(\\E zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S))))" (is "\\E x : ?z_hhm(x)")
   by (rule zenon_notallex_0 [of "?z_hhj", OF z_Hhc])
   have z_Hhn: "?z_hhm((CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S)))))" (is "~(?z_hhp=>?z_hhq)")
   by (rule zenon_ex_choose_0 [of "?z_hhm", OF z_Hhk])
   have z_Hhp: "?z_hhp"
   by (rule zenon_notimply_0 [OF z_Hhn])
   have z_Hhr: "(~?z_hhq)"
   by (rule zenon_notimply_1 [OF z_Hhn])
   have z_Hhs: "((CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S)))) \\in ?z_hl)" (is "?z_hhs")
   by (rule zenon_in_setminus_0 [of "(CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S))))" "?z_hl" "{m}", OF z_Hhp])
   show FALSE
   proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vxo. (~(zenon_Vxo \\in S)))" "(?z_hl \\ {m})" "(\<lambda>s. (pi[s]))" "(CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S))))", OF z_Hhr])
    assume z_Hhx:"(~?z_hhp)"
    show FALSE
    by (rule notE [OF z_Hhx z_Hhp])
   next
    assume z_Hhy:"(~((pi[(CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S))))]) \\in S))" (is "~?z_hhz")
    have z_Hib: "(\\A zenon_Vw:((zenon_Vw \\in ?z_hl)=>((pi[zenon_Vw]) \\in S)))" (is "\\A x : ?z_hih(x)")
    by (rule zenon_in_funcset_2 [of "pi" "?z_hl" "S", OF z_Hfu])
    have z_Hii: "?z_hih((CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S)))))"
    by (rule zenon_all_0 [of "?z_hih" "(CHOOSE zenon_Vto:(~((zenon_Vto \\in (?z_hl \\ {m}))=>((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[zenon_Vto]) \\in S))))", OF z_Hib])
    show FALSE
    proof (rule zenon_imply [OF z_Hii])
     assume z_Hij:"(~?z_hhs)"
     show FALSE
     by (rule notE [OF z_Hij z_Hhs])
    next
     assume z_Hhz:"?z_hhz"
     show FALSE
     by (rule notE [OF z_Hhy z_Hhz])
    qed
   qed
  qed
 next
  assume z_Hgs:"?z_hgs" (is "?z_hik=>_")
  show FALSE
  proof (rule zenon_imply [OF z_Hgs])
   assume z_Hil:"(~?z_hik)"
   have z_Him_z_Hil: "(~(\\A x:((x \\in S)=>bEx((?z_hl \\ {m}), (\<lambda>s. ((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))) == (~?z_hik)" (is "?z_him == ?z_hil")
   by (unfold bAll_def)
   have z_Him: "?z_him" (is "~(\\A x : ?z_hio(x))")
   by (unfold z_Him_z_Hil, fact z_Hil)
   have z_Hip: "(\\E x:(~((x \\in S)=>bEx((?z_hl \\ {m}), (\<lambda>s. ((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[s])=x))))))" (is "\\E x : ?z_hiq(x)")
   by (rule zenon_notallex_0 [of "?z_hio", OF z_Him])
   have z_Hir: "?z_hiq((CHOOSE x:(~((x \\in S)=>bEx((?z_hl \\ {m}), (\<lambda>s. ((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))" (is "~(?z_hfh=>?z_his)")
   by (rule zenon_ex_choose_0 [of "?z_hiq", OF z_Hip])
   have z_Hfh: "?z_hfh"
   by (rule zenon_notimply_0 [OF z_Hir])
   have z_Hit: "(~?z_his)"
   by (rule zenon_notimply_1 [OF z_Hir])
   have z_Hds_z_Hit: "(~(\\E x:((x \\in (?z_hl \\ {m}))&((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[x])=(CHOOSE x:(~((x \\in S)=>bEx((?z_hl \\ {m}), (\<lambda>s. ((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))))) == (~?z_his)" (is "?z_hds == ?z_hit")
   by (unfold bEx_def)
   have z_Hds: "?z_hds" (is "~(\\E x : ?z_hdz(x))")
   by (unfold z_Hds_z_Hit, fact z_Hit)
   have z_Hiu: "~?z_hdz(k)" (is "~(?z_hcd&?z_hiv)")
   by (rule zenon_notex_0 [of "?z_hdz" "k", OF z_Hds])
   show FALSE
   proof (rule zenon_notand [OF z_Hiu])
    assume z_Hcc:"(~?z_hcd)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hcc z_He z_Hc z_Hcf])
   next
    assume z_Hiw:"((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[k])~=(CHOOSE x:(~((x \\in S)=>bEx((?z_hl \\ {m}), (\<lambda>s. ((Fcn((?z_hl \\ {m}), (\<lambda>s. (pi[s])))[s])=x)))))))" (is "?z_hix~=?z_hcy")
    show FALSE
    proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vdc. (zenon_Vdc~=?z_hcy))" "(?z_hl \\ {m})" "(\<lambda>s. (pi[s]))" "k", OF z_Hiw])
     assume z_Hcc:"(~?z_hcd)"
     show FALSE
     by (rule zenon_L2_ [OF z_Hcc z_He z_Hc z_Hcf])
    next
     assume z_Hfo:"(?z_hbc~=?z_hcy)"
     show FALSE
     by (rule zenon_L6_ [OF z_Hfo z_Hf z_Hfb z_Hfh z_Hds])
    qed
   qed
  next
   assume z_Hfs:"?z_hfs"
   show FALSE
   by (rule notE [OF z_Hh z_Hfs])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
lemma ob'6:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
assumes v'147: "((\<And> S :: c. (((IsFiniteSet ((S)))) \<Longrightarrow> (\<And> pi :: c. pi \<in> ((Perm ((S)))) \<Longrightarrow> (\<And> k :: c. k \<in> ((DOMAIN (pi))) \<Longrightarrow> (\<And> m :: c. m \<in> ((DOMAIN (pi))) \<Longrightarrow> ((((k) \<noteq> (m))) \<Longrightarrow> ((((fapply ((pi), (k))) = (fapply ((pi), (m))))) \<Longrightarrow> (FALSE)))))))))"
shows "(\<forall>S : ((((IsFiniteSet ((S)))) \<Rightarrow> (\<forall> pi \<in> ((Perm ((S)))) : (\<forall> k \<in> ((DOMAIN (pi))) : (\<forall> m \<in> ((DOMAIN (pi))) : (((((k) \<noteq> (m))) \<Rightarrow> (((fapply ((pi), (k))) \<noteq> (fapply ((pi), (m)))))))))))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_0d62a0.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_0d62a0.znn.out
;; obligation #6
$hyp "v'147" (A. ((S) (=> (IsFiniteSet S) (TLA.bAll (Perm S) ((pi) (TLA.bAll (TLA.DOMAIN pi) ((k) (TLA.bAll (TLA.DOMAIN pi) ((m) (=> (-. (= k
m)) (=> (= (TLA.fapply pi k)
(TLA.fapply pi m)) F.)))))))))))
$goal (A. ((S) (=> (IsFiniteSet S)
(TLA.bAll (Perm S) ((pi) (TLA.bAll (TLA.DOMAIN pi) ((k) (TLA.bAll (TLA.DOMAIN pi) ((m) (=> (-. (= k
m)) (-. (= (TLA.fapply pi k)
(TLA.fapply pi m)))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(\\A S:(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>(((pi[k])=(pi[m]))=>FALSE))))))))))" (is "\\A x : ?z_hx(x)")
 using v'147 by blast
 have zenon_L1_: "bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>k. bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((k~=m)=>((((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[k])=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))=>FALSE)))))) ==> ((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m])))))))) \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m])))))))))))) ==> ((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>(((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=x)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x]))))))) ==> (((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>(((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=x)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x]))))))])) ==> ((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>(((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=x)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])))))) \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m])))))))))))) ==> FALSE" (is "?z_hy ==> ?z_hci ==> ?z_hct ==> ?z_hdb ==> ?z_hdd ==> FALSE")
 proof -
  assume z_Hy:"?z_hy"
  assume z_Hci:"?z_hci"
  assume z_Hct:"?z_hct" (is "?z_hcj~=?z_hcu")
  assume z_Hdb:"?z_hdb" (is "?z_hda=?z_hdc")
  assume z_Hdd:"?z_hdd"
  have z_Hde_z_Hy: "(\\A x:((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>((((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))=>FALSE)))))) == ?z_hy" (is "?z_hde == _")
  by (unfold bAll_def)
  have z_Hde: "?z_hde" (is "\\A x : ?z_hdl(x)")
  by (unfold z_Hde_z_Hy, fact z_Hy)
  have z_Hdm: "?z_hdl(?z_hcu)" (is "_=>?z_hdn")
  by (rule zenon_all_0 [of "?z_hdl" "?z_hcu", OF z_Hde])
  show FALSE
  proof (rule zenon_imply [OF z_Hdm])
   assume z_Hdo:"(~?z_hdd)"
   show FALSE
   by (rule notE [OF z_Hdo z_Hdd])
  next
   assume z_Hdn:"?z_hdn"
   have z_Hdp_z_Hdn: "(\\A x:((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>((?z_hcu~=x)=>((?z_hdc=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x]))=>FALSE)))) == ?z_hdn" (is "?z_hdp == _")
   by (unfold bAll_def)
   have z_Hdp: "?z_hdp" (is "\\A x : ?z_hdv(x)")
   by (unfold z_Hdp_z_Hdn, fact z_Hdn)
   have z_Hdw: "?z_hdv(?z_hcj)" (is "_=>?z_hdx")
   by (rule zenon_all_0 [of "?z_hdv" "?z_hcj", OF z_Hdp])
   show FALSE
   proof (rule zenon_imply [OF z_Hdw])
    assume z_Hdy:"(~?z_hci)"
    show FALSE
    by (rule notE [OF z_Hdy z_Hci])
   next
    assume z_Hdx:"?z_hdx" (is "?z_hdz=>?z_hea")
    show FALSE
    proof (rule zenon_imply [OF z_Hdx])
     assume z_Heb:"(~?z_hdz)" (is "~~?z_hec")
     have z_Hec: "?z_hec"
     by (rule zenon_notnot_0 [OF z_Heb])
     show FALSE
     by (rule zenon_eqsym [OF z_Hec z_Hct])
    next
     assume z_Hea:"?z_hea" (is "?z_hed=>?z_hw")
     show FALSE
     proof (rule zenon_imply [OF z_Hea])
      assume z_Hee:"(?z_hdc~=?z_hda)"
      show FALSE
      by (rule zenon_eqsym [OF z_Hdb z_Hee])
     next
      assume z_Hw:"?z_hw"
      show FALSE
      by (rule z_Hw)
     qed
    qed
   qed
  qed
 qed
 assume z_Hb:"(~(\\A S:(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))" (is "~(\\A x : ?z_heg(x))")
 have z_Heh: "(\\E S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))" (is "\\E x : ?z_hei(x)")
 by (rule zenon_notallex_0 [of "?z_heg", OF z_Hb])
 have z_Hej: "?z_hei((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m])))))))))))))" (is "~(?z_hek=>?z_hel)")
 by (rule zenon_ex_choose_0 [of "?z_hei", OF z_Heh])
 have z_Hek: "?z_hek"
 by (rule zenon_notimply_0 [OF z_Hej])
 have z_Hem: "(~?z_hel)"
 by (rule zenon_notimply_1 [OF z_Hej])
 have z_Hen_z_Hem: "(~(\\A x:((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m])))))))))) == (~?z_hel)" (is "?z_hen == ?z_hem")
 by (unfold bAll_def)
 have z_Hen: "?z_hen" (is "~(\\A x : ?z_hep(x))")
 by (unfold z_Hen_z_Hem, fact z_Hem)
 have z_Heq: "(\\E x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))" (is "\\E x : ?z_her(x)")
 by (rule zenon_notallex_0 [of "?z_hep", OF z_Hen])
 have z_Hes: "?z_her((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m])))))))))))" (is "~(?z_het=>?z_heu)")
 by (rule zenon_ex_choose_0 [of "?z_her", OF z_Heq])
 have z_Het: "?z_het"
 by (rule zenon_notimply_0 [OF z_Hes])
 have z_Hev: "(~?z_heu)"
 by (rule zenon_notimply_1 [OF z_Hes])
 have z_Hew_z_Hev: "(~(\\A x:((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m])))))))) == (~?z_heu)" (is "?z_hew == ?z_hev")
 by (unfold bAll_def)
 have z_Hew: "?z_hew" (is "~(\\A x : ?z_hey(x))")
 by (unfold z_Hew_z_Hev, fact z_Hev)
 have z_Hez: "(\\E x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))" (is "\\E x : ?z_hfa(x)")
 by (rule zenon_notallex_0 [of "?z_hey", OF z_Hew])
 have z_Hfb: "?z_hfa((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m])))))))))" (is "~(?z_hci=>?z_hfc)")
 by (rule zenon_ex_choose_0 [of "?z_hfa", OF z_Hez])
 have z_Hci: "?z_hci"
 by (rule zenon_notimply_0 [OF z_Hfb])
 have z_Hfd: "(~?z_hfc)"
 by (rule zenon_notimply_1 [OF z_Hfb])
 have z_Hfe_z_Hfd: "(~(\\A x:((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>(((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=x)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])))))) == (~?z_hfc)" (is "?z_hfe == ?z_hfd")
 by (unfold bAll_def)
 have z_Hfe: "?z_hfe" (is "~(\\A x : ?z_hfg(x))")
 by (unfold z_Hfe_z_Hfd, fact z_Hfd)
 have z_Hfh: "(\\E x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>(((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=x)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x]))))))" (is "\\E x : ?z_hfi(x)")
 by (rule zenon_notallex_0 [of "?z_hfg", OF z_Hfe])
 have z_Hfj: "?z_hfi((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>(((CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))~=x)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[(CHOOSE x:(~((x \\in DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))))=>bAll(DOMAIN((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))), (\<lambda>m. ((x~=m)=>(((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[m]))))))))])~=((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))[x])))))))" (is "~(?z_hdd=>?z_hfk)")
 by (rule zenon_ex_choose_0 [of "?z_hfi", OF z_Hfh])
 have z_Hdd: "?z_hdd"
 by (rule zenon_notimply_0 [OF z_Hfj])
 have z_Hfl: "(~?z_hfk)" (is "~(?z_hct=>?z_hfm)")
 by (rule zenon_notimply_1 [OF z_Hfj])
 have z_Hct: "?z_hct" (is "?z_hcj~=?z_hcu")
 by (rule zenon_notimply_0 [OF z_Hfl])
 have z_Hfn: "(~?z_hfm)" (is "~~?z_hdb")
 by (rule zenon_notimply_1 [OF z_Hfl])
 have z_Hdb: "?z_hdb" (is "?z_hda=?z_hdc")
 by (rule zenon_notnot_0 [OF z_Hfn])
 have z_Hfo: "?z_hx((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m])))))))))))))" (is "_=>?z_hfp")
 by (rule zenon_all_0 [of "?z_hx" "(CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))", OF z_Ha])
 show FALSE
 proof (rule zenon_imply [OF z_Hfo])
  assume z_Hfq:"(~?z_hek)"
  show FALSE
  by (rule notE [OF z_Hfq z_Hek])
 next
  assume z_Hfp:"?z_hfp"
  have z_Hfr_z_Hfp: "(\\A x:((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>(((x[k])=(x[m]))=>FALSE)))))))) == ?z_hfp" (is "?z_hfr == _")
  by (unfold bAll_def)
  have z_Hfr: "?z_hfr" (is "\\A x : ?z_hga(x)")
  by (unfold z_Hfr_z_Hfp, fact z_Hfp)
  have z_Hgb: "?z_hga((CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m])))))))))))" (is "_=>?z_hy")
  by (rule zenon_all_0 [of "?z_hga" "(CHOOSE x:(~((x \\in Perm((CHOOSE S:(~(IsFiniteSet(S)=>bAll(Perm(S), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))))))))=>bAll(DOMAIN(x), (\<lambda>k. bAll(DOMAIN(x), (\<lambda>m. ((k~=m)=>((x[k])~=(x[m]))))))))))", OF z_Hfr])
  show FALSE
  proof (rule zenon_imply [OF z_Hgb])
   assume z_Hgc:"(~?z_het)"
   show FALSE
   by (rule notE [OF z_Hgc z_Het])
  next
   assume z_Hy:"?z_hy"
   show FALSE
   by (rule zenon_L1_ [OF z_Hy z_Hci z_Hct z_Hdb z_Hdd])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
lemma ob'213:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'183: "((((((((A) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((A)))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n))))))))))))) & (((s) \<notin> (A))))"
assumes v'184: "((((Cardinality ((((A) \<union> ({(s)})))))) = ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))"
assumes v'185: "(\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (m))), (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (n))))))))))"
assumes v'186: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]) \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"
shows "(((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))"(is "PROP ?ob'213")
proof -
ML_command {* writeln "*** TLAPS ENTER 213"; *}
show "PROP ?ob'213"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_152871.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_152871.znn.out
;; obligation #213
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) A))
$hyp "v'183" (/\ (=> (/\ (TLA.in A (TLA.SUBSET arith.Z)) (IsFiniteSet A))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (Cardinality A))
A) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) ((n) (=> (arith.lt m n) (arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n)))))))))) (-. (TLA.in s
A)))
$hyp "v'184" (= (Cardinality (TLA.cup A (TLA.set s)))
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))
$hyp "v'185" (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) m)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) n)))))))
$hyp "v'186" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))))))
(Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$goal (=> (/\ (TLA.in (TLA.cup A (TLA.set s)) (TLA.SUBSET arith.Z))
(IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>m. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>n. ((m < n)=>((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[m]) < (Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))" (is "?z_hh")
 using v'185 by blast
 have z_Hg:"(Cardinality((A \\cup {s}))=(Cardinality(A) + 1))" (is "?z_hbj=?z_hm")
 using v'184 by blast
 have z_Hi:"(Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))) \\in Bijection(isa'dotdot(1, ?z_hm), (A \\cup {s})))" (is "?z_hi")
 using v'186 by blast
 have zenon_L1_: "(isa'dotdot(1, ?z_hbj)~=isa'dotdot(1, ?z_hm)) ==> (?z_hbj=?z_hm) ==> FALSE" (is "?z_hbn ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hbn:"?z_hbn" (is "?z_hbo~=?z_hk")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_noteq [of "?z_hk"])
   have z_Hbp: "(?z_hk~=?z_hk)"
   by (rule subst [where P="(\<lambda>zenon_Vbp. (isa'dotdot(1, zenon_Vbp)~=?z_hk))", OF z_Hg], fact z_Hbn)
   thus "(?z_hk~=?z_hk)" .
  qed
 qed
 assume z_Hj:"(~((((A \\cup {s}) \\in SUBSET(Int))&IsFiniteSet((A \\cup {s})))=>bEx(Bijection(isa'dotdot(1, ?z_hbj), (A \\cup {s})), (\<lambda>f_1. bAll(isa'dotdot(1, ?z_hbj), (\<lambda>m. bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((m < n)=>((f_1[m]) < (f_1[n])))))))))))" (is "~(?z_hbv=>?z_hby)")
 have z_Hck_z_Hh: "(\\A x:((x \\in isa'dotdot(1, ?z_hm))=>bAll(isa'dotdot(1, ?z_hm), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))) == ?z_hh" (is "?z_hck == _")
 by (unfold bAll_def)
 have z_Hck: "?z_hck" (is "\\A x : ?z_hcu(x)")
 by (unfold z_Hck_z_Hh, fact z_Hh)
 have z_Hcv: "(~?z_hby)"
 by (rule zenon_notimply_1 [OF z_Hj])
 have z_Hcw_z_Hcv: "(~(\\E x:((x \\in Bijection(isa'dotdot(1, ?z_hbj), (A \\cup {s})))&bAll(isa'dotdot(1, ?z_hbj), (\<lambda>m. bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((m < n)=>((x[m]) < (x[n])))))))))) == (~?z_hby)" (is "?z_hcw == ?z_hcv")
 by (unfold bEx_def)
 have z_Hcw: "?z_hcw" (is "~(\\E x : ?z_hdi(x))")
 by (unfold z_Hcw_z_Hcv, fact z_Hcv)
 have z_Hdj: "~?z_hdi(Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))))" (is "~(?z_hdk&?z_hdl)")
 by (rule zenon_notex_0 [of "?z_hdi" "Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))", OF z_Hcw])
 show FALSE
 proof (rule zenon_notand [OF z_Hdj])
  assume z_Hdm:"(~?z_hdk)"
  show FALSE
  proof (rule notE [OF z_Hdm])
   have z_Hdn: "(Bijection(isa'dotdot(1, ?z_hm), (A \\cup {s}))=Bijection(isa'dotdot(1, ?z_hbj), (A \\cup {s})))" (is "?z_hbm=?z_hbz")
   proof (rule zenon_nnpp [of "(?z_hbm=?z_hbz)"])
    assume z_Hdo:"(?z_hbm~=?z_hbz)"
    show FALSE
    proof (rule zenon_noteq [of "?z_hbz"])
     have z_Hdp: "(isa'dotdot(1, ?z_hm)=isa'dotdot(1, ?z_hbj))" (is "?z_hk=?z_hbo")
     proof (rule zenon_nnpp [of "(?z_hk=?z_hbo)"])
      assume z_Hdq:"(?z_hk~=?z_hbo)"
      show FALSE
      proof (rule zenon_noteq [of "?z_hbo"])
       have z_Hdr: "(?z_hm=?z_hbj)"
       by (rule sym [OF z_Hg])
       have z_Hds: "(?z_hbo~=?z_hbo)"
       by (rule subst [where P="(\<lambda>zenon_Vkp. (isa'dotdot(1, zenon_Vkp)~=?z_hbo))", OF z_Hdr], fact z_Hdq)
       thus "(?z_hbo~=?z_hbo)" .
      qed
     qed
     have z_Hdx: "(?z_hbz~=?z_hbz)"
     by (rule subst [where P="(\<lambda>zenon_Vjp. (Bijection(zenon_Vjp, (A \\cup {s}))~=?z_hbz))", OF z_Hdp], fact z_Hdo)
     thus "(?z_hbz~=?z_hbz)" .
    qed
   qed
   have z_Hdk: "?z_hdk"
   by (rule subst [where P="(\<lambda>zenon_Vh. (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))) \\in zenon_Vh))", OF z_Hdn], fact z_Hi)
   thus "?z_hdk" .
  qed
 next
  assume z_Hef:"(~?z_hdl)"
  have z_Heg_z_Hef: "(~(\\A x:((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) == (~?z_hdl)" (is "?z_heg == ?z_hef")
  by (unfold bAll_def)
  have z_Heg: "?z_heg" (is "~(\\A x : ?z_hel(x))")
  by (unfold z_Heg_z_Hef, fact z_Hef)
  have z_Hem: "(\\E x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))" (is "\\E x : ?z_heo(x)")
  by (rule zenon_notallex_0 [of "?z_hel", OF z_Heg])
  have z_Hep: "?z_heo((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))))" (is "~(?z_her=>?z_hes)")
  by (rule zenon_ex_choose_0 [of "?z_heo", OF z_Hem])
  have z_Her: "?z_her"
  by (rule zenon_notimply_0 [OF z_Hep])
  have z_Het: "(~?z_hes)"
  by (rule zenon_notimply_1 [OF z_Hep])
  have z_Heu_z_Het: "(~(\\A x:((x \\in isa'dotdot(1, ?z_hbj))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x])))))) == (~?z_hes)" (is "?z_heu == ?z_het")
  by (unfold bAll_def)
  have z_Heu: "?z_heu" (is "~(\\A x : ?z_hfb(x))")
  by (unfold z_Heu_z_Het, fact z_Het)
  have z_Hfc: "(\\E x:(~((x \\in isa'dotdot(1, ?z_hbj))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]))))))" (is "\\E x : ?z_hfe(x)")
  by (rule zenon_notallex_0 [of "?z_hfb", OF z_Heu])
  have z_Hff: "?z_hfe((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x])))))))" (is "~(?z_hfh=>?z_hfi)")
  by (rule zenon_ex_choose_0 [of "?z_hfe", OF z_Hfc])
  have z_Hfh: "?z_hfh"
  by (rule zenon_notimply_0 [OF z_Hff])
  have z_Hfj: "(~?z_hfi)" (is "~(?z_hfk=>?z_hfl)")
  by (rule zenon_notimply_1 [OF z_Hff])
  have z_Hfk: "?z_hfk"
  by (rule zenon_notimply_0 [OF z_Hfj])
  have z_Hfm: "(~?z_hfl)"
  by (rule zenon_notimply_1 [OF z_Hfj])
  have z_Hfn: "?z_hcu((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))))" (is "?z_hfo=>?z_hfp")
  by (rule zenon_all_0 [of "?z_hcu" "(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))", OF z_Hck])
  show FALSE
  proof (rule zenon_imply [OF z_Hfn])
   assume z_Hfq:"(~?z_hfo)"
   show FALSE
   proof (rule notE [OF z_Hfq])
    have z_Hfr: "(isa'dotdot(1, ?z_hbj)=isa'dotdot(1, ?z_hm))" (is "?z_hbo=?z_hk")
    proof (rule zenon_nnpp [of "(?z_hbo=?z_hk)"])
     assume z_Hbn:"(?z_hbo~=?z_hk)"
     show FALSE
     by (rule zenon_L1_ [OF z_Hbn z_Hg])
    qed
    have z_Hfo: "?z_hfo"
    by (rule subst [where P="(\<lambda>zenon_Vwi. ((CHOOSE x:(~((x \\in ?z_hbo)=>bAll(?z_hbo, (\<lambda>n. ((x < n)=>((Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) \\in zenon_Vwi))", OF z_Hfr], fact z_Her)
    thus "?z_hfo" .
   qed
  next
   assume z_Hfp:"?z_hfp"
   have z_Hfv_z_Hfp: "(\\A x:((x \\in isa'dotdot(1, ?z_hm))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]))))) == ?z_hfp" (is "?z_hfv == _")
   by (unfold bAll_def)
   have z_Hfv: "?z_hfv" (is "\\A x : ?z_hfx(x)")
   by (unfold z_Hfv_z_Hfp, fact z_Hfp)
   have z_Hfy: "?z_hfx((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x])))))))" (is "?z_hfz=>_")
   by (rule zenon_all_0 [of "?z_hfx" "(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbj))=>bAll(isa'dotdot(1, ?z_hbj), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]))))))", OF z_Hfv])
   show FALSE
   proof (rule zenon_imply [OF z_Hfy])
    assume z_Hga:"(~?z_hfz)"
    show FALSE
    proof (rule notE [OF z_Hga])
     have z_Hfr: "(isa'dotdot(1, ?z_hbj)=isa'dotdot(1, ?z_hm))" (is "?z_hbo=?z_hk")
     proof (rule zenon_nnpp [of "(?z_hbo=?z_hk)"])
      assume z_Hbn:"(?z_hbo~=?z_hk)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hbn z_Hg])
     qed
     have z_Hfz: "?z_hfz"
     by (rule subst [where P="(\<lambda>zenon_Vdj. ((CHOOSE x:(~((x \\in ?z_hbo)=>(((CHOOSE x:(~((x \\in ?z_hbo)=>bAll(?z_hbo, (\<lambda>n. ((x < n)=>((Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in ?z_hbo)=>bAll(?z_hbo, (\<lambda>n. ((x < n)=>((Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x]) < (Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(?z_hk, (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[x])))))) \\in zenon_Vdj))", OF z_Hfr], fact z_Hfh)
     thus "?z_hfz" .
    qed
   next
    assume z_Hfi:"?z_hfi"
    show FALSE
    proof (rule zenon_imply [OF z_Hfi])
     assume z_Hge:"(~?z_hfk)"
     show FALSE
     by (rule notE [OF z_Hge z_Hfk])
    next
     assume z_Hfl:"?z_hfl"
     show FALSE
     by (rule notE [OF z_Hfm z_Hfl])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 213"; *} qed
lemma ob'190:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'182: "((\<And> b :: c. b \<in> (((A) \<union> ({(s)}))) \<Longrightarrow> (\<exists> a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : (((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (a))) = (b))))))"
assumes v'183: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]) \<in> ([((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<rightarrow> (((A) \<union> ({(s)})))])))"
assumes v'184: "((\<And> S_1 :: c. (\<And> T :: c. (\<And> F :: c. F \<in> ([(S_1) \<rightarrow> (T)]) \<Longrightarrow> ((\<forall> t \<in> (T) : (\<exists> s_1 \<in> (S_1) : (((fapply ((F), (s_1))) = (t))))) \<Longrightarrow> (((F) \<in> ((Surjection ((S_1), (T)))))))))))"
shows "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]) \<in> ((Surjection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"(is "PROP ?ob'190")
proof -
ML_command {* writeln "*** TLAPS ENTER 190"; *}
show "PROP ?ob'190"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_bb455d.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_bb455d.znn.out
;; obligation #190
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) A))
$hyp "v'182" (TLA.bAll (TLA.cup A
(TLA.set s)) ((b) (TLA.bEx (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((a) (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) a)
b)))))
$hyp "v'183" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k))))
(TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$hyp "v'184" (A. ((S_1) (A. ((T) (TLA.bAll (TLA.FuncSet S_1 T) ((F) (=> (TLA.bAll T ((t) (TLA.bEx S_1 ((s_1) (= (TLA.fapply F s_1)
t))))) (TLA.in F (Surjection S_1
T)))))))))
$goal (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k))))
(Surjection (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A S_1:(\\A T:bAll(FuncSet(S_1, T), (\<lambda>F. (bAll(T, (\<lambda>t. bEx(S_1, (\<lambda>s_1. ((F[s_1])=t)))))=>(F \\in Surjection(S_1, T)))))))" (is "\\A x : ?z_hbb(x)")
 using v'184 by blast
 have z_Hf:"bAll((A \\cup {s}), (\<lambda>b. bEx(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. ((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[a])=b)))))" (is "?z_hf")
 using v'182 by blast
 have z_Hg:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k])))) \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hg")
 using v'183 by blast
 assume z_Hi:"(~(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k])))) \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))))" (is "~?z_hbz")
 have z_Hcb: "?z_hbb(isa'dotdot(1, (Cardinality(A) + 1)))" (is "\\A x : ?z_hcc(x)")
 by (rule zenon_all_0 [of "?z_hbb" "isa'dotdot(1, (Cardinality(A) + 1))", OF z_Hh])
 have z_Hcd: "?z_hcc((A \\cup {s}))" (is "?z_hcd")
 by (rule zenon_all_0 [of "?z_hcc" "(A \\cup {s})", OF z_Hcb])
 have z_Hce_z_Hcd: "(\\A x:((x \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))=>(bAll((A \\cup {s}), (\<lambda>t. bEx(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>s_1. ((x[s_1])=t)))))=>(x \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))))) == ?z_hcd" (is "?z_hce == _")
 by (unfold bAll_def)
 have z_Hce: "?z_hce" (is "\\A x : ?z_hcq(x)")
 by (unfold z_Hce_z_Hcd, fact z_Hcd)
 have z_Hcr: "?z_hcq(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k])))))" (is "_=>?z_hcs")
 by (rule zenon_all_0 [of "?z_hcq" "Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))", OF z_Hce])
 show FALSE
 proof (rule zenon_imply [OF z_Hcr])
  assume z_Hct:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hct z_Hg])
 next
  assume z_Hcs:"?z_hcs"
  show FALSE
  proof (rule zenon_imply [OF z_Hcs])
   assume z_Hcu:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hcu z_Hf])
  next
   assume z_Hbz:"?z_hbz"
   show FALSE
   by (rule notE [OF z_Hi z_Hbz])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 190"; *} qed
lemma ob'171:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
fixes a
assumes a_in : "(a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))))"
fixes b
assumes b_in : "(b \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))))"
assumes v'183: "(((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (a))) = (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (b)))))"
assumes v'193: "(((((A) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((A))))))"
assumes v'194: "(((f) \<in> ((Perm ((A))))))"
assumes v'195: "((((DOMAIN (f))) = ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A)))))))))"
assumes v'196: "(((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (a))) = (fapply ((f), (a)))))"
assumes v'197: "(((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (b))) = (fapply ((f), (b)))))"
assumes v'198: "(((((a) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))) \<and> (((b) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A)))))))))))"
assumes v'199: "(\<forall>S_1 : ((((IsFiniteSet ((S_1)))) \<Rightarrow> (\<forall> pi \<in> ((Perm ((S_1)))) : (\<forall> k \<in> ((DOMAIN (pi))) : (\<forall> m \<in> ((DOMAIN (pi))) : (((((k) \<noteq> (m))) \<Rightarrow> (((fapply ((pi), (k))) \<noteq> (fapply ((pi), (m)))))))))))))"
shows "(((a) = (b)))"(is "PROP ?ob'171")
proof -
ML_command {* writeln "*** TLAPS ENTER 171"; *}
show "PROP ?ob'171"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_b52b0c.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_b52b0c.znn.out
;; obligation #171
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "a_in" (TLA.in a (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))))
$hyp "b_in" (TLA.in b (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))))
$hyp "v'183" (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) a)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) b))
$hyp "v'193" (/\ (TLA.in A (TLA.SUBSET arith.Z))
(IsFiniteSet A))
$hyp "v'194" (TLA.in f (Perm A))
$hyp "v'195" (= (TLA.DOMAIN f) (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)))
$hyp "v'196" (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) a)
(TLA.fapply f a))
$hyp "v'197" (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) b)
(TLA.fapply f b))
$hyp "v'198" (/\ (TLA.in a (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))) (TLA.in b (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))))
$hyp "v'199" (A. ((S_1) (=> (IsFiniteSet S_1)
(TLA.bAll (Perm S_1) ((pi) (TLA.bAll (TLA.DOMAIN pi) ((k) (TLA.bAll (TLA.DOMAIN pi) ((m) (=> (-. (= k
m)) (-. (= (TLA.fapply pi k) (TLA.fapply pi m)))))))))))))
$goal (= a
b)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"((A \\in SUBSET(Int))&IsFiniteSet(A))" (is "?z_hq&?z_hu")
 using v'193 by blast
 have z_Hk:"(DOMAIN(f)=isa'dotdot(1, Cardinality(A)))" (is "?z_hv=?z_hx")
 using v'195 by blast
 have z_Hh:"((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[a])=(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[b]))" (is "?z_hba=?z_hbl")
 using v'183 by blast
 have z_Hm:"(?z_hbl=(f[b]))" (is "_=?z_hbn")
 using v'197 by blast
 have z_Hl:"(?z_hba=(f[a]))" (is "_=?z_hbo")
 using v'196 by blast
 have z_Hj:"(f \\in Perm(A))" (is "?z_hj")
 using v'194 by blast
 have z_Ho:"(\\A S_1:(IsFiniteSet(S_1)=>bAll(Perm(S_1), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m])))))))))))" (is "\\A x : ?z_hci(x)")
 using v'199 by blast
 have z_Hn:"((a \\in ?z_hx)&(b \\in ?z_hx))" (is "?z_hcj&?z_hck")
 using v'198 by blast
 have zenon_L1_: "(\\A zenon_Vm:((zenon_Vm \\in ?z_hv)<=>(zenon_Vm \\in ?z_hx))) ==> ?z_hcj ==> (~(a \\in ?z_hv)) ==> FALSE" (is "?z_hcl ==> _ ==> ?z_hcq ==> FALSE")
 proof -
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hcs(x)")
  assume z_Hcj:"?z_hcj"
  assume z_Hcq:"?z_hcq" (is "~?z_hcr")
  have z_Hct: "?z_hcs(a)"
  by (rule zenon_all_0 [of "?z_hcs" "a", OF z_Hcl])
  show FALSE
  proof (rule zenon_equiv [OF z_Hct])
   assume z_Hcq:"?z_hcq"
   assume z_Hcu:"(~?z_hcj)"
   show FALSE
   by (rule notE [OF z_Hcu z_Hcj])
  next
   assume z_Hcr:"?z_hcr"
   assume z_Hcj:"?z_hcj"
   show FALSE
   by (rule notE [OF z_Hcq z_Hcr])
  qed
 qed
 have zenon_L2_: "(\\A zenon_Vm:((zenon_Vm \\in ?z_hv)<=>(zenon_Vm \\in ?z_hx))) ==> ?z_hck ==> (~(b \\in ?z_hv)) ==> FALSE" (is "?z_hcl ==> _ ==> ?z_hcv ==> FALSE")
 proof -
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hcs(x)")
  assume z_Hck:"?z_hck"
  assume z_Hcv:"?z_hcv" (is "~?z_hcw")
  have z_Hcx: "?z_hcs(b)"
  by (rule zenon_all_0 [of "?z_hcs" "b", OF z_Hcl])
  show FALSE
  proof (rule zenon_equiv [OF z_Hcx])
   assume z_Hcv:"?z_hcv"
   assume z_Hcy:"(~?z_hck)"
   show FALSE
   by (rule notE [OF z_Hcy z_Hck])
  next
   assume z_Hcw:"?z_hcw"
   assume z_Hck:"?z_hck"
   show FALSE
   by (rule notE [OF z_Hcv z_Hcw])
  qed
 qed
 have zenon_L3_: "bAll(?z_hv, (\<lambda>k. bAll(?z_hv, (\<lambda>m. ((k~=m)=>((f[k])~=(f[m]))))))) ==> ?z_hck ==> (a~=b) ==> (?z_hba=?z_hbl) ==> (?z_hbl=?z_hbn) ==> (?z_hba=?z_hbo) ==> ?z_hcj ==> (\\A zenon_Vm:((zenon_Vm \\in ?z_hv)<=>(zenon_Vm \\in ?z_hx))) ==> FALSE" (is "?z_hcz ==> _ ==> ?z_hp ==> ?z_hh ==> ?z_hm ==> ?z_hl ==> _ ==> ?z_hcl ==> FALSE")
 proof -
  assume z_Hcz:"?z_hcz"
  assume z_Hck:"?z_hck"
  assume z_Hp:"?z_hp"
  assume z_Hh:"?z_hh"
  assume z_Hm:"?z_hm"
  assume z_Hl:"?z_hl"
  assume z_Hcj:"?z_hcj"
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hcs(x)")
  have z_Hdg_z_Hcz: "(\\A x:((x \\in ?z_hv)=>bAll(?z_hv, (\<lambda>m. ((x~=m)=>((f[x])~=(f[m]))))))) == ?z_hcz" (is "?z_hdg == _")
  by (unfold bAll_def)
  have z_Hdg: "?z_hdg" (is "\\A x : ?z_hdq(x)")
  by (unfold z_Hdg_z_Hcz, fact z_Hcz)
  have z_Hdr: "?z_hdq(a)" (is "?z_hcr=>?z_hds")
  by (rule zenon_all_0 [of "?z_hdq" "a", OF z_Hdg])
  show FALSE
  proof (rule zenon_imply [OF z_Hdr])
   assume z_Hcq:"(~?z_hcr)"
   show FALSE
   by (rule zenon_L1_ [OF z_Hcl z_Hcj z_Hcq])
  next
   assume z_Hds:"?z_hds"
   have z_Hdt_z_Hds: "(\\A x:((x \\in ?z_hv)=>((a~=x)=>(?z_hbo~=(f[x]))))) == ?z_hds" (is "?z_hdt == _")
   by (unfold bAll_def)
   have z_Hdt: "?z_hdt" (is "\\A x : ?z_hdy(x)")
   by (unfold z_Hdt_z_Hds, fact z_Hds)
   have z_Hdz: "?z_hdy(b)" (is "?z_hcw=>?z_hea")
   by (rule zenon_all_0 [of "?z_hdy" "b", OF z_Hdt])
   show FALSE
   proof (rule zenon_imply [OF z_Hdz])
    assume z_Hcv:"(~?z_hcw)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hcl z_Hck z_Hcv])
   next
    assume z_Hea:"?z_hea" (is "_=>?z_heb")
    show FALSE
    proof (rule zenon_imply [OF z_Hea])
     assume z_Hec:"(~?z_hp)" (is "~~?z_hed")
     show FALSE
     by (rule notE [OF z_Hec z_Hp])
    next
     assume z_Heb:"?z_heb"
     show FALSE
     proof (rule notE [OF z_Heb])
      have z_Hee: "(?z_hbo=?z_hbl)"
      by (rule subst [where P="(\<lambda>zenon_Vq. (zenon_Vq=?z_hbl))", OF z_Hl], fact z_Hh)
      have z_Hei: "(?z_hbo=?z_hbn)"
      by (rule subst [where P="(\<lambda>zenon_Vac. (?z_hbo=zenon_Vac))", OF z_Hm], fact z_Hee)
      thus "(?z_hbo=?z_hbn)" .
     qed
    qed
   qed
  qed
 qed
 assume z_Hp:"(a~=b)"
 have z_Hu: "?z_hu"
 by (rule zenon_and_1 [OF z_Hi])
 have z_Hcj: "?z_hcj"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hck: "?z_hck"
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hcl: "(\\A zenon_Vm:((zenon_Vm \\in ?z_hv)<=>(zenon_Vm \\in ?z_hx)))" (is "\\A x : ?z_hcs(x)")
 by (rule zenon_setequal_0 [of "?z_hv" "?z_hx", OF z_Hk])
 have z_Hem: "?z_hci(A)" (is "_=>?z_hen")
 by (rule zenon_all_0 [of "?z_hci" "A", OF z_Ho])
 show FALSE
 proof (rule zenon_imply [OF z_Hem])
  assume z_Heo:"(~?z_hu)"
  show FALSE
  by (rule notE [OF z_Heo z_Hu])
 next
  assume z_Hen:"?z_hen"
  have z_Hcz: "bAll(?z_hv, (\<lambda>k. bAll(?z_hv, (\<lambda>m. ((k~=m)=>((f[k])~=(f[m])))))))" (is "?z_hcz")
  by (rule zenon_all_in_0 [of "Perm(A)" "(\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))", OF z_Hen z_Hj])
  show FALSE
  by (rule zenon_L3_ [OF z_Hcz z_Hck z_Hp z_Hh z_Hm z_Hl z_Hcj z_Hcl])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 171"; *} qed
lemma ob'141:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'181: "((\<And> a :: c. a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<Longrightarrow> (\<And> b :: c. b \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<Longrightarrow> ((((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (a))) = (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (b))))) \<Longrightarrow> (((a) = (b)))))))"
assumes v'182: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]) \<in> ([((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<rightarrow> (((A) \<union> ({(s)})))])))"
assumes v'183: "((\<And> S_1 :: c. (\<And> T :: c. (\<And> F :: c. F \<in> ([(S_1) \<rightarrow> (T)]) \<Longrightarrow> ((\<forall> a \<in> (S_1) : (\<forall> b \<in> (S_1) : (((((fapply ((F), (a))) = (fapply ((F), (b))))) \<Rightarrow> (((a) = (b))))))) \<Longrightarrow> (((F) \<in> ((Injection ((S_1), (T)))))))))))"
shows "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]) \<in> ((Injection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"(is "PROP ?ob'141")
proof -
ML_command {* writeln "*** TLAPS ENTER 141"; *}
show "PROP ?ob'141"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_bbf4cb.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_bbf4cb.znn.out
;; obligation #141
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "v'181" (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((a) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((b) (=> (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) a)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) b)) (= a
b))))))
$hyp "v'182" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k))))
(TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$hyp "v'183" (A. ((S_1) (A. ((T) (TLA.bAll (TLA.FuncSet S_1 T) ((F) (=> (TLA.bAll S_1 ((a) (TLA.bAll S_1 ((b) (=> (= (TLA.fapply F a)
(TLA.fapply F b)) (= a b)))))) (TLA.in F (Injection S_1
T)))))))))
$goal (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k))))
(Injection (arith.intrange (TLA.fapply TLA.Succ 0) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A S_1:(\\A T:bAll(FuncSet(S_1, T), (\<lambda>F. (bAll(S_1, (\<lambda>a. bAll(S_1, (\<lambda>b. (((F[a])=(F[b]))=>(a=b))))))=>(F \\in Injection(S_1, T)))))))" (is "\\A x : ?z_hbe(x)")
 using v'183 by blast
 have z_Hf:"bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>b. (((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[a])=(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[b]))=>(a=b))))))" (is "?z_hf")
 using v'181 by blast
 have z_Hg:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k])))) \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hg")
 using v'182 by blast
 assume z_Hi:"(~(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k])))) \\in Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))))" (is "~?z_hcc")
 have z_Hce: "?z_hbe(isa'dotdot(1, (Cardinality(A) + 1)))" (is "\\A x : ?z_hcf(x)")
 by (rule zenon_all_0 [of "?z_hbe" "isa'dotdot(1, (Cardinality(A) + 1))", OF z_Hh])
 have z_Hcg: "?z_hcf((A \\cup {s}))" (is "?z_hcg")
 by (rule zenon_all_0 [of "?z_hcf" "(A \\cup {s})", OF z_Hce])
 have z_Hch_z_Hcg: "(\\A x:((x \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))=>(bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>b. (((x[a])=(x[b]))=>(a=b))))))=>(x \\in Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))))) == ?z_hcg" (is "?z_hch == _")
 by (unfold bAll_def)
 have z_Hch: "?z_hch" (is "\\A x : ?z_hcv(x)")
 by (unfold z_Hch_z_Hcg, fact z_Hcg)
 have z_Hcw: "?z_hcv(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k])))))" (is "_=>?z_hcx")
 by (rule zenon_all_0 [of "?z_hcv" "Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))", OF z_Hch])
 show FALSE
 proof (rule zenon_imply [OF z_Hcw])
  assume z_Hcy:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hcy z_Hg])
 next
  assume z_Hcx:"?z_hcx"
  show FALSE
  proof (rule zenon_imply [OF z_Hcx])
   assume z_Hcz:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hcz z_Hf])
  next
   assume z_Hcc:"?z_hcc"
   show FALSE
   by (rule notE [OF z_Hi z_Hcc])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 141"; *} qed
lemma ob'93:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'182: "((((((((A) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((A)))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n))))))))))))) & (((s) \<notin> (A))))"
assumes v'183: "((((Cardinality ((((A) \<union> ({(s)})))))) = ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))"
assumes v'184: "(\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (m))), (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]), (n))))))))))"
assumes v'185: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))), (s), (fapply ((f), (k)))))]) \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"
shows "(((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))"(is "PROP ?ob'93")
proof -
ML_command {* writeln "*** TLAPS ENTER 93"; *}
show "PROP ?ob'93"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_6ae3ce.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_6ae3ce.znn.out
;; obligation #93
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) A))
$hyp "v'182" (/\ (=> (/\ (TLA.in A (TLA.SUBSET arith.Z)) (IsFiniteSet A))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (Cardinality A))
A) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) ((n) (=> (arith.lt m n) (arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n)))))))))) (-. (TLA.in s
A)))
$hyp "v'183" (= (Cardinality (TLA.cup A (TLA.set s)))
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))
$hyp "v'184" (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) m)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) s (TLA.fapply f k)))) n)))))))
$hyp "v'185" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) s (TLA.fapply f k))))
(Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$goal (=> (/\ (TLA.in (TLA.cup A (TLA.set s)) (TLA.SUBSET arith.Z))
(IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>m. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>n. ((m < n)=>((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[m]) < (Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=(Cardinality(A) + 1)), s, (f[k]))))[n])))))))" (is "?z_hh")
 using v'184 by blast
 have z_Hg:"(Cardinality((A \\cup {s}))=(Cardinality(A) + 1))" (is "?z_hbh=?z_hm")
 using v'183 by blast
 have z_Hi:"(Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k])))) \\in Bijection(isa'dotdot(1, ?z_hm), (A \\cup {s})))" (is "?z_hi")
 using v'185 by blast
 have zenon_L1_: "(isa'dotdot(1, ?z_hbh)~=isa'dotdot(1, ?z_hm)) ==> (?z_hbh=?z_hm) ==> FALSE" (is "?z_hbl ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hbl:"?z_hbl" (is "?z_hbm~=?z_hk")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_noteq [of "?z_hk"])
   have z_Hbn: "(?z_hk~=?z_hk)"
   by (rule subst [where P="(\<lambda>zenon_Vtk. (isa'dotdot(1, zenon_Vtk)~=?z_hk))", OF z_Hg], fact z_Hbl)
   thus "(?z_hk~=?z_hk)" .
  qed
 qed
 assume z_Hj:"(~((((A \\cup {s}) \\in SUBSET(Int))&IsFiniteSet((A \\cup {s})))=>bEx(Bijection(isa'dotdot(1, ?z_hbh), (A \\cup {s})), (\<lambda>f_1. bAll(isa'dotdot(1, ?z_hbh), (\<lambda>m. bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((m < n)=>((f_1[m]) < (f_1[n])))))))))))" (is "~(?z_hbt=>?z_hbw)")
 have z_Hci_z_Hh: "(\\A x:((x \\in isa'dotdot(1, ?z_hm))=>bAll(isa'dotdot(1, ?z_hm), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))) == ?z_hh" (is "?z_hci == _")
 by (unfold bAll_def)
 have z_Hci: "?z_hci" (is "\\A x : ?z_hcs(x)")
 by (unfold z_Hci_z_Hh, fact z_Hh)
 have z_Hct: "(~?z_hbw)"
 by (rule zenon_notimply_1 [OF z_Hj])
 have z_Hcu_z_Hct: "(~(\\E x:((x \\in Bijection(isa'dotdot(1, ?z_hbh), (A \\cup {s})))&bAll(isa'dotdot(1, ?z_hbh), (\<lambda>m. bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((m < n)=>((x[m]) < (x[n])))))))))) == (~?z_hbw)" (is "?z_hcu == ?z_hct")
 by (unfold bEx_def)
 have z_Hcu: "?z_hcu" (is "~(\\E x : ?z_hdg(x))")
 by (unfold z_Hcu_z_Hct, fact z_Hct)
 have z_Hdh: "~?z_hdg(Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k])))))" (is "~(?z_hdi&?z_hdj)")
 by (rule zenon_notex_0 [of "?z_hdg" "Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))", OF z_Hcu])
 show FALSE
 proof (rule zenon_notand [OF z_Hdh])
  assume z_Hdk:"(~?z_hdi)"
  show FALSE
  proof (rule notE [OF z_Hdk])
   have z_Hdl: "(Bijection(isa'dotdot(1, ?z_hm), (A \\cup {s}))=Bijection(isa'dotdot(1, ?z_hbh), (A \\cup {s})))" (is "?z_hbk=?z_hbx")
   proof (rule zenon_nnpp [of "(?z_hbk=?z_hbx)"])
    assume z_Hdm:"(?z_hbk~=?z_hbx)"
    show FALSE
    proof (rule zenon_noteq [of "?z_hbx"])
     have z_Hdn: "(isa'dotdot(1, ?z_hm)=isa'dotdot(1, ?z_hbh))" (is "?z_hk=?z_hbm")
     proof (rule zenon_nnpp [of "(?z_hk=?z_hbm)"])
      assume z_Hdo:"(?z_hk~=?z_hbm)"
      show FALSE
      proof (rule zenon_noteq [of "?z_hbm"])
       have z_Hdp: "(?z_hm=?z_hbh)"
       by (rule sym [OF z_Hg])
       have z_Hdq: "(?z_hbm~=?z_hbm)"
       by (rule subst [where P="(\<lambda>zenon_Vcaa. (isa'dotdot(1, zenon_Vcaa)~=?z_hbm))", OF z_Hdp], fact z_Hdo)
       thus "(?z_hbm~=?z_hbm)" .
      qed
     qed
     have z_Hdv: "(?z_hbx~=?z_hbx)"
     by (rule subst [where P="(\<lambda>zenon_Vbaa. (Bijection(zenon_Vbaa, (A \\cup {s}))~=?z_hbx))", OF z_Hdn], fact z_Hdm)
     thus "(?z_hbx~=?z_hbx)" .
    qed
   qed
   have z_Hdi: "?z_hdi"
   by (rule subst [where P="(\<lambda>zenon_Vh. (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k])))) \\in zenon_Vh))", OF z_Hdl], fact z_Hi)
   thus "?z_hdi" .
  qed
 next
  assume z_Hed:"(~?z_hdj)"
  have z_Hee_z_Hed: "(~(\\A x:((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) == (~?z_hdj)" (is "?z_hee == ?z_hed")
  by (unfold bAll_def)
  have z_Hee: "?z_hee" (is "~(\\A x : ?z_hej(x))")
  by (unfold z_Hee_z_Hed, fact z_Hed)
  have z_Hek: "(\\E x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))" (is "\\E x : ?z_hem(x)")
  by (rule zenon_notallex_0 [of "?z_hej", OF z_Hee])
  have z_Hen: "?z_hem((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))))" (is "~(?z_hep=>?z_heq)")
  by (rule zenon_ex_choose_0 [of "?z_hem", OF z_Hek])
  have z_Hep: "?z_hep"
  by (rule zenon_notimply_0 [OF z_Hen])
  have z_Her: "(~?z_heq)"
  by (rule zenon_notimply_1 [OF z_Hen])
  have z_Hes_z_Her: "(~(\\A x:((x \\in isa'dotdot(1, ?z_hbh))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x])))))) == (~?z_heq)" (is "?z_hes == ?z_her")
  by (unfold bAll_def)
  have z_Hes: "?z_hes" (is "~(\\A x : ?z_hez(x))")
  by (unfold z_Hes_z_Her, fact z_Her)
  have z_Hfa: "(\\E x:(~((x \\in isa'dotdot(1, ?z_hbh))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]))))))" (is "\\E x : ?z_hfc(x)")
  by (rule zenon_notallex_0 [of "?z_hez", OF z_Hes])
  have z_Hfd: "?z_hfc((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x])))))))" (is "~(?z_hff=>?z_hfg)")
  by (rule zenon_ex_choose_0 [of "?z_hfc", OF z_Hfa])
  have z_Hff: "?z_hff"
  by (rule zenon_notimply_0 [OF z_Hfd])
  have z_Hfh: "(~?z_hfg)" (is "~(?z_hfi=>?z_hfj)")
  by (rule zenon_notimply_1 [OF z_Hfd])
  have z_Hfi: "?z_hfi"
  by (rule zenon_notimply_0 [OF z_Hfh])
  have z_Hfk: "(~?z_hfj)"
  by (rule zenon_notimply_1 [OF z_Hfh])
  have z_Hfl: "?z_hcs((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))))" (is "?z_hfm=>?z_hfn")
  by (rule zenon_all_0 [of "?z_hcs" "(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))", OF z_Hci])
  show FALSE
  proof (rule zenon_imply [OF z_Hfl])
   assume z_Hfo:"(~?z_hfm)"
   show FALSE
   proof (rule notE [OF z_Hfo])
    have z_Hfp: "(isa'dotdot(1, ?z_hbh)=isa'dotdot(1, ?z_hm))" (is "?z_hbm=?z_hk")
    proof (rule zenon_nnpp [of "(?z_hbm=?z_hk)"])
     assume z_Hbl:"(?z_hbm~=?z_hk)"
     show FALSE
     by (rule zenon_L1_ [OF z_Hbl z_Hg])
    qed
    have z_Hfm: "?z_hfm"
    by (rule subst [where P="(\<lambda>zenon_Ves. ((CHOOSE x:(~((x \\in ?z_hbm)=>bAll(?z_hbm, (\<lambda>n. ((x < n)=>((Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) \\in zenon_Ves))", OF z_Hfp], fact z_Hep)
    thus "?z_hfm" .
   qed
  next
   assume z_Hfn:"?z_hfn"
   have z_Hft_z_Hfn: "(\\A x:((x \\in isa'dotdot(1, ?z_hm))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]))))) == ?z_hfn" (is "?z_hft == _")
   by (unfold bAll_def)
   have z_Hft: "?z_hft" (is "\\A x : ?z_hfv(x)")
   by (unfold z_Hft_z_Hfn, fact z_Hfn)
   have z_Hfw: "?z_hfv((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x])))))))" (is "?z_hfx=>_")
   by (rule zenon_all_0 [of "?z_hfv" "(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbh))=>bAll(isa'dotdot(1, ?z_hbh), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_hm), (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]))))))", OF z_Hft])
   show FALSE
   proof (rule zenon_imply [OF z_Hfw])
    assume z_Hfy:"(~?z_hfx)"
    show FALSE
    proof (rule notE [OF z_Hfy])
     have z_Hfp: "(isa'dotdot(1, ?z_hbh)=isa'dotdot(1, ?z_hm))" (is "?z_hbm=?z_hk")
     proof (rule zenon_nnpp [of "(?z_hbm=?z_hk)"])
      assume z_Hbl:"(?z_hbm~=?z_hk)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hbl z_Hg])
     qed
     have z_Hfx: "?z_hfx"
     by (rule subst [where P="(\<lambda>zenon_Vls. ((CHOOSE x:(~((x \\in ?z_hbm)=>(((CHOOSE x:(~((x \\in ?z_hbm)=>bAll(?z_hbm, (\<lambda>n. ((x < n)=>((Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n])))))))) < x)=>((Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[(CHOOSE x:(~((x \\in ?z_hbm)=>bAll(?z_hbm, (\<lambda>n. ((x < n)=>((Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x]) < (Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[n]))))))))]) < (Fcn(?z_hk, (\<lambda>k. cond((k=?z_hm), s, (f[k]))))[x])))))) \\in zenon_Vls))", OF z_Hfp], fact z_Hff)
     thus "?z_hfx" .
    qed
   next
    assume z_Hfg:"?z_hfg"
    show FALSE
    proof (rule zenon_imply [OF z_Hfg])
     assume z_Hgc:"(~?z_hfi)"
     show FALSE
     by (rule notE [OF z_Hgc z_Hfi])
    next
     assume z_Hfj:"?z_hfj"
     show FALSE
     by (rule notE [OF z_Hfk z_Hfj])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 93"; *} qed
lemma ob'363:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'184: "(((((((subsetOf((A), %z. ((less ((z), (s)))))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((subsetOf((A), %z. ((less ((z), (s))))))))))) \<and> (((subsetOf((A), %z. ((less ((z), (s)))))) \<noteq> ({})))))"
assumes v'185: "(\<forall>S_1 : (((((((((S_1) \<in> ((SUBSET (Int))))) \<and> (((S_1) \<noteq> ({}))))) \<and> ((IsFiniteSet ((S_1)))))) \<Rightarrow> (\<exists> s_1 \<in> (S_1) : (\<forall> y \<in> (S_1) : ((leq ((y), (s_1)))))))))"
shows "(\<exists> pred \<in> (subsetOf((A), %z. ((less ((z), (s)))))) : (\<forall> y \<in> (subsetOf((A), %z. ((less ((z), (s)))))) : ((leq ((y), (pred))))))"(is "PROP ?ob'363")
proof -
ML_command {* writeln "*** TLAPS ENTER 363"; *}
show "PROP ?ob'363"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_67d862.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_67d862.znn.out
;; obligation #363
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "v'184" (/\ (/\ (TLA.in (TLA.subsetOf A ((z) (arith.lt z s)))
(TLA.SUBSET arith.Z)) (IsFiniteSet (TLA.subsetOf A ((z) (arith.lt z s)))))
(-. (= (TLA.subsetOf A ((z) (arith.lt z s)))
TLA.emptyset)))
$hyp "v'185" (A. ((S_1) (=> (/\ (/\ (TLA.in S_1 (TLA.SUBSET arith.Z))
(-. (= S_1 TLA.emptyset))) (IsFiniteSet S_1))
(TLA.bEx S_1 ((s_1) (TLA.bAll S_1 ((y) (arith.le y
s_1))))))))
$goal (TLA.bEx (TLA.subsetOf A ((z) (arith.lt z
s))) ((pred) (TLA.bAll (TLA.subsetOf A ((z) (arith.lt z s))) ((y) (arith.le y
pred)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"(((subsetOf(A, (\<lambda>z. (z < s))) \\in SUBSET(Int))&IsFiniteSet(subsetOf(A, (\<lambda>z. (z < s)))))&(subsetOf(A, (\<lambda>z. (z < s)))~={}))" (is "?z_hi&?z_ht")
 using v'184 by blast
 have z_Hg:"(\\A S_1:((((S_1 \\in SUBSET(Int))&(S_1~={}))&IsFiniteSet(S_1))=>bEx(S_1, (\<lambda>s_1. bAll(S_1, (\<lambda>y. (y <= s_1)))))))" (is "\\A x : ?z_hbj(x)")
 using v'185 by blast
 assume z_Hh:"(~bEx(subsetOf(A, (\<lambda>z. (z < s))), (\<lambda>pred. bAll(subsetOf(A, (\<lambda>z. (z < s))), (\<lambda>y. (y <= pred))))))" (is "~?z_hbk")
 have z_Hi: "?z_hi" (is "?z_hj&?z_hs")
 by (rule zenon_and_0 [OF z_Hf])
 have z_Ht: "?z_ht" (is "?z_hk~=_")
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hj: "?z_hj"
 by (rule zenon_and_0 [OF z_Hi])
 have z_Hs: "?z_hs"
 by (rule zenon_and_1 [OF z_Hi])
 have z_Hbq: "?z_hbj(?z_hk)" (is "?z_hbr=>_")
 by (rule zenon_all_0 [of "?z_hbj" "?z_hk", OF z_Hg])
 show FALSE
 proof (rule zenon_imply [OF z_Hbq])
  assume z_Hbs:"(~?z_hbr)" (is "~(?z_hbt&_)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbs])
   assume z_Hbu:"(~?z_hbt)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbu])
    assume z_Hbv:"(~?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbv z_Hj])
   next
    assume z_Hbw:"(~?z_ht)" (is "~~?z_hbx")
    show FALSE
    by (rule notE [OF z_Hbw z_Ht])
   qed
  next
   assume z_Hby:"(~?z_hs)"
   show FALSE
   by (rule notE [OF z_Hby z_Hs])
  qed
 next
  assume z_Hbk:"?z_hbk"
  show FALSE
  by (rule notE [OF z_Hh z_Hbk])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 363"; *} qed
lemma ob'346:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
fixes pred
assumes pred_in : "(pred \<in> (subsetOf((A), %z. ((less ((z), (s)))))))"
fixes a_predunde_ka
assumes a_predunde_ka_in : "(a_predunde_ka \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
assumes v'200: "((((((((A) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((A)))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n))))))))))))) & (((s) \<notin> (A))))"
assumes v'201: "((((Cardinality ((((A) \<union> ({(s)})))))) = ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))"
assumes v'202: "(\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]), (m))), (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]), (n))))))))))"
assumes v'203: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]) \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"
shows "(((((((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((((A) \<union> ({(s)})))))))) \<Rightarrow> (\<exists> f_1 \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))), (((A) \<union> ({(s)})))))) : (\<forall> m \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : (\<forall> n \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((((A) \<union> ({(s)}))))))))) : ((((less ((m), (n)))) \<Rightarrow> ((less ((fapply ((f_1), (m))), (fapply ((f_1), (n)))))))))))))"(is "PROP ?ob'346")
proof -
ML_command {* writeln "*** TLAPS ENTER 346"; *}
show "PROP ?ob'346"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_ee2f13.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_ee2f13.znn.out
;; obligation #346
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "pred_in" (TLA.in pred (TLA.subsetOf A ((z) (arith.lt z
s))))
$hyp "a_predunde_ka_in" (TLA.in a_predunde_ka (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)))
$hyp "v'200" (/\ (=> (/\ (TLA.in A (TLA.SUBSET arith.Z)) (IsFiniteSet A))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (Cardinality A))
A) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) ((n) (=> (arith.lt m n) (arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n)))))))))) (-. (TLA.in s
A)))
$hyp "v'201" (= (Cardinality (TLA.cup A (TLA.set s)))
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))
$hyp "v'202" (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) ))) m)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) ))) n)))))))
$hyp "v'203" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) )))
(Bijection (arith.intrange (TLA.fapply TLA.Succ 0) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$goal (=> (/\ (TLA.in (TLA.cup A (TLA.set s)) (TLA.SUBSET arith.Z))
(IsFiniteSet (TLA.cup A (TLA.set s))))
(TLA.bEx (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) (TLA.cup A
(TLA.set s))) ((f_1) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A
(TLA.set s)))) ((m) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality (TLA.cup A (TLA.set s)))) ((n) (=> (arith.lt m n)
(arith.lt (TLA.fapply f_1 m)
(TLA.fapply f_1 n))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>m. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>n. ((m < n)=>((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))]))))[m]) < (Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))]))))[n])))))))" (is "?z_hj")
 using v'202 by blast
 have z_Hi:"(Cardinality((A \\cup {s}))=(Cardinality(A) + 1))" (is "?z_hbu=?z_ho")
 using v'201 by blast
 have z_Hk:"(Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))])))) \\in Bijection(isa'dotdot(1, ?z_ho), (A \\cup {s})))" (is "?z_hk")
 using v'203 by blast
 have zenon_L1_: "(isa'dotdot(1, ?z_hbu)~=isa'dotdot(1, ?z_ho)) ==> (?z_hbu=?z_ho) ==> FALSE" (is "?z_hby ==> ?z_hi ==> FALSE")
 proof -
  assume z_Hby:"?z_hby" (is "?z_hbz~=?z_hm")
  assume z_Hi:"?z_hi"
  show FALSE
  proof (rule zenon_noteq [of "?z_hm"])
   have z_Hca: "(?z_hm~=?z_hm)"
   by (rule subst [where P="(\<lambda>zenon_Vpn. (isa'dotdot(1, zenon_Vpn)~=?z_hm))", OF z_Hi], fact z_Hby)
   thus "(?z_hm~=?z_hm)" .
  qed
 qed
 assume z_Hl:"(~((((A \\cup {s}) \\in SUBSET(Int))&IsFiniteSet((A \\cup {s})))=>bEx(Bijection(isa'dotdot(1, ?z_hbu), (A \\cup {s})), (\<lambda>f_1. bAll(isa'dotdot(1, ?z_hbu), (\<lambda>m. bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((m < n)=>((f_1[m]) < (f_1[n])))))))))))" (is "~(?z_hcg=>?z_hcj)")
 have z_Hcv_z_Hj: "(\\A x:((x \\in isa'dotdot(1, ?z_ho))=>bAll(isa'dotdot(1, ?z_ho), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))) == ?z_hj" (is "?z_hcv == _")
 by (unfold bAll_def)
 have z_Hcv: "?z_hcv" (is "\\A x : ?z_hdf(x)")
 by (unfold z_Hcv_z_Hj, fact z_Hj)
 have z_Hdg: "(~?z_hcj)"
 by (rule zenon_notimply_1 [OF z_Hl])
 have z_Hdh_z_Hdg: "(~(\\E x:((x \\in Bijection(isa'dotdot(1, ?z_hbu), (A \\cup {s})))&bAll(isa'dotdot(1, ?z_hbu), (\<lambda>m. bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((m < n)=>((x[m]) < (x[n])))))))))) == (~?z_hcj)" (is "?z_hdh == ?z_hdg")
 by (unfold bEx_def)
 have z_Hdh: "?z_hdh" (is "~(\\E x : ?z_hdt(x))")
 by (unfold z_Hdh_z_Hdg, fact z_Hdg)
 have z_Hdu: "~?z_hdt(Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))])))))" (is "~(?z_hdv&?z_hdw)")
 by (rule zenon_notex_0 [of "?z_hdt" "Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))", OF z_Hdh])
 show FALSE
 proof (rule zenon_notand [OF z_Hdu])
  assume z_Hdx:"(~?z_hdv)"
  show FALSE
  proof (rule notE [OF z_Hdx])
   have z_Hdy: "(Bijection(isa'dotdot(1, ?z_ho), (A \\cup {s}))=Bijection(isa'dotdot(1, ?z_hbu), (A \\cup {s})))" (is "?z_hbx=?z_hck")
   proof (rule zenon_nnpp [of "(?z_hbx=?z_hck)"])
    assume z_Hdz:"(?z_hbx~=?z_hck)"
    show FALSE
    proof (rule zenon_noteq [of "?z_hck"])
     have z_Hea: "(isa'dotdot(1, ?z_ho)=isa'dotdot(1, ?z_hbu))" (is "?z_hm=?z_hbz")
     proof (rule zenon_nnpp [of "(?z_hm=?z_hbz)"])
      assume z_Heb:"(?z_hm~=?z_hbz)"
      show FALSE
      proof (rule zenon_noteq [of "?z_hbz"])
       have z_Hec: "(?z_ho=?z_hbu)"
       by (rule sym [OF z_Hi])
       have z_Hed: "(?z_hbz~=?z_hbz)"
       by (rule subst [where P="(\<lambda>zenon_Vyn. (isa'dotdot(1, zenon_Vyn)~=?z_hbz))", OF z_Hec], fact z_Heb)
       thus "(?z_hbz~=?z_hbz)" .
      qed
     qed
     have z_Hei: "(?z_hck~=?z_hck)"
     by (rule subst [where P="(\<lambda>zenon_Vxn. (Bijection(zenon_Vxn, (A \\cup {s}))~=?z_hck))", OF z_Hea], fact z_Hdz)
     thus "(?z_hck~=?z_hck)" .
    qed
   qed
   have z_Hdv: "?z_hdv"
   by (rule subst [where P="(\<lambda>zenon_Vh. (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))])))) \\in zenon_Vh))", OF z_Hdy], fact z_Hk)
   thus "?z_hdv" .
  qed
 next
  assume z_Heq:"(~?z_hdw)"
  have z_Her_z_Heq: "(~(\\A x:((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) == (~?z_hdw)" (is "?z_her == ?z_heq")
  by (unfold bAll_def)
  have z_Her: "?z_her" (is "~(\\A x : ?z_hew(x))")
  by (unfold z_Her_z_Heq, fact z_Heq)
  have z_Hex: "(\\E x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))" (is "\\E x : ?z_hez(x)")
  by (rule zenon_notallex_0 [of "?z_hew", OF z_Her])
  have z_Hfa: "?z_hez((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))))" (is "~(?z_hfc=>?z_hfd)")
  by (rule zenon_ex_choose_0 [of "?z_hez", OF z_Hex])
  have z_Hfc: "?z_hfc"
  by (rule zenon_notimply_0 [OF z_Hfa])
  have z_Hfe: "(~?z_hfd)"
  by (rule zenon_notimply_1 [OF z_Hfa])
  have z_Hff_z_Hfe: "(~(\\A x:((x \\in isa'dotdot(1, ?z_hbu))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x])))))) == (~?z_hfd)" (is "?z_hff == ?z_hfe")
  by (unfold bAll_def)
  have z_Hff: "?z_hff" (is "~(\\A x : ?z_hfm(x))")
  by (unfold z_Hff_z_Hfe, fact z_Hfe)
  have z_Hfn: "(\\E x:(~((x \\in isa'dotdot(1, ?z_hbu))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]))))))" (is "\\E x : ?z_hfp(x)")
  by (rule zenon_notallex_0 [of "?z_hfm", OF z_Hff])
  have z_Hfq: "?z_hfp((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x])))))))" (is "~(?z_hfs=>?z_hft)")
  by (rule zenon_ex_choose_0 [of "?z_hfp", OF z_Hfn])
  have z_Hfs: "?z_hfs"
  by (rule zenon_notimply_0 [OF z_Hfq])
  have z_Hfu: "(~?z_hft)" (is "~(?z_hfv=>?z_hfw)")
  by (rule zenon_notimply_1 [OF z_Hfq])
  have z_Hfv: "?z_hfv"
  by (rule zenon_notimply_0 [OF z_Hfu])
  have z_Hfx: "(~?z_hfw)"
  by (rule zenon_notimply_1 [OF z_Hfu])
  have z_Hfy: "?z_hdf((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))))" (is "?z_hfz=>?z_hga")
  by (rule zenon_all_0 [of "?z_hdf" "(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))", OF z_Hcv])
  show FALSE
  proof (rule zenon_imply [OF z_Hfy])
   assume z_Hgb:"(~?z_hfz)"
   show FALSE
   proof (rule notE [OF z_Hgb])
    have z_Hgc: "(isa'dotdot(1, ?z_hbu)=isa'dotdot(1, ?z_ho))" (is "?z_hbz=?z_hm")
    proof (rule zenon_nnpp [of "(?z_hbz=?z_hm)"])
     assume z_Hby:"(?z_hbz~=?z_hm)"
     show FALSE
     by (rule zenon_L1_ [OF z_Hby z_Hi])
    qed
    have z_Hfz: "?z_hfz"
    by (rule subst [where P="(\<lambda>zenon_Vnj. ((CHOOSE x:(~((x \\in ?z_hbz)=>bAll(?z_hbz, (\<lambda>n. ((x < n)=>((Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) \\in zenon_Vnj))", OF z_Hgc], fact z_Hfc)
    thus "?z_hfz" .
   qed
  next
   assume z_Hga:"?z_hga"
   have z_Hgg_z_Hga: "(\\A x:((x \\in isa'dotdot(1, ?z_ho))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]))))) == ?z_hga" (is "?z_hgg == _")
   by (unfold bAll_def)
   have z_Hgg: "?z_hgg" (is "\\A x : ?z_hgi(x)")
   by (unfold z_Hgg_z_Hga, fact z_Hga)
   have z_Hgj: "?z_hgi((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x])))))))" (is "?z_hgk=>_")
   by (rule zenon_all_0 [of "?z_hgi" "(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>(((CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in isa'dotdot(1, ?z_hbu))=>bAll(isa'dotdot(1, ?z_hbu), (\<lambda>n. ((x < n)=>((Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(isa'dotdot(1, ?z_ho), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]))))))", OF z_Hgg])
   show FALSE
   proof (rule zenon_imply [OF z_Hgj])
    assume z_Hgl:"(~?z_hgk)"
    show FALSE
    proof (rule notE [OF z_Hgl])
     have z_Hgc: "(isa'dotdot(1, ?z_hbu)=isa'dotdot(1, ?z_ho))" (is "?z_hbz=?z_hm")
     proof (rule zenon_nnpp [of "(?z_hbz=?z_hm)"])
      assume z_Hby:"(?z_hbz~=?z_hm)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hby z_Hi])
     qed
     have z_Hgk: "?z_hgk"
     by (rule subst [where P="(\<lambda>zenon_Vuj. ((CHOOSE x:(~((x \\in ?z_hbz)=>(((CHOOSE x:(~((x \\in ?z_hbz)=>bAll(?z_hbz, (\<lambda>n. ((x < n)=>((Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n])))))))) < x)=>((Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[(CHOOSE x:(~((x \\in ?z_hbz)=>bAll(?z_hbz, (\<lambda>n. ((x < n)=>((Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x]) < (Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[n]))))))))]) < (Fcn(?z_hm, (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), ?z_ho)) -> (f[(k +  -.(1))]))))[x])))))) \\in zenon_Vuj))", OF z_Hgc], fact z_Hfs)
     thus "?z_hgk" .
    qed
   next
    assume z_Hft:"?z_hft"
    show FALSE
    proof (rule zenon_imply [OF z_Hft])
     assume z_Hgp:"(~?z_hfv)"
     show FALSE
     by (rule notE [OF z_Hgp z_Hfv])
    next
     assume z_Hfw:"?z_hfw"
     show FALSE
     by (rule notE [OF z_Hfx z_Hfw])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 346"; *} qed
lemma ob'323:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'183: "((\<And> b :: c. b \<in> (((A) \<union> ({(s)}))) \<Longrightarrow> (\<exists> a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : (((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (a))) = (b))))))"
assumes v'184: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]) \<in> ([((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<rightarrow> (((A) \<union> ({(s)})))])))"
assumes v'185: "((\<And> S_1 :: c. (\<And> T :: c. (\<And> F :: c. F \<in> ([(S_1) \<rightarrow> (T)]) \<Longrightarrow> ((\<forall> t \<in> (T) : (\<exists> s_1 \<in> (S_1) : (((fapply ((F), (s_1))) = (t))))) \<Longrightarrow> (((F) \<in> ((Surjection ((S_1), (T)))))))))))"
shows "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]) \<in> ((Surjection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"(is "PROP ?ob'323")
proof -
ML_command {* writeln "*** TLAPS ENTER 323"; *}
show "PROP ?ob'323"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_cd4a80.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_cd4a80.znn.out
;; obligation #323
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) A))
$hyp "v'183" (TLA.bAll (TLA.cup A
(TLA.set s)) ((b) (TLA.bEx (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((a) (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) a)
b)))))
$hyp "v'184" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))))))
(TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$hyp "v'185" (A. ((S_1) (A. ((T) (TLA.bAll (TLA.FuncSet S_1 T) ((F) (=> (TLA.bAll T ((t) (TLA.bEx S_1 ((s_1) (= (TLA.fapply F s_1)
t))))) (TLA.in F (Surjection S_1
T)))))))))
$goal (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))))))
(Surjection (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A S_1:(\\A T:bAll(FuncSet(S_1, T), (\<lambda>F. (bAll(T, (\<lambda>t. bEx(S_1, (\<lambda>s_1. ((F[s_1])=t)))))=>(F \\in Surjection(S_1, T)))))))" (is "\\A x : ?z_hbb(x)")
 using v'185 by blast
 have z_Hf:"bAll((A \\cup {s}), (\<lambda>b. bEx(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. ((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[a])=b)))))" (is "?z_hf")
 using v'183 by blast
 have z_Hg:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))) \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hg")
 using v'184 by blast
 assume z_Hi:"(~(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))) \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))))" (is "~?z_hcb")
 have z_Hcd: "?z_hbb(isa'dotdot(1, (Cardinality(A) + 1)))" (is "\\A x : ?z_hce(x)")
 by (rule zenon_all_0 [of "?z_hbb" "isa'dotdot(1, (Cardinality(A) + 1))", OF z_Hh])
 have z_Hcf: "?z_hce((A \\cup {s}))" (is "?z_hcf")
 by (rule zenon_all_0 [of "?z_hce" "(A \\cup {s})", OF z_Hcd])
 have z_Hcg_z_Hcf: "(\\A x:((x \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))=>(bAll((A \\cup {s}), (\<lambda>t. bEx(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>s_1. ((x[s_1])=t)))))=>(x \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))))) == ?z_hcf" (is "?z_hcg == _")
 by (unfold bAll_def)
 have z_Hcg: "?z_hcg" (is "\\A x : ?z_hcs(x)")
 by (unfold z_Hcg_z_Hcf, fact z_Hcf)
 have z_Hct: "?z_hcs(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))))" (is "_=>?z_hcu")
 by (rule zenon_all_0 [of "?z_hcs" "Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))", OF z_Hcg])
 show FALSE
 proof (rule zenon_imply [OF z_Hct])
  assume z_Hcv:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hcv z_Hg])
 next
  assume z_Hcu:"?z_hcu"
  show FALSE
  proof (rule zenon_imply [OF z_Hcu])
   assume z_Hcw:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hcw z_Hf])
  next
   assume z_Hcb:"?z_hcb"
   show FALSE
   by (rule notE [OF z_Hi z_Hcb])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 323"; *} qed
lemma ob'310:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
fixes a
assumes a_in : "(a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))))"
fixes b
assumes b_in : "(b \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))))"
assumes v'184: "(((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (a))) = (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (b)))))"
assumes v'196: "(((((A) \<in> ((SUBSET (Int))))) \<and> ((IsFiniteSet ((A))))))"
assumes v'197: "((((DOMAIN (f))) = ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A)))))))))"
assumes v'198: "(((f) \<in> ((Perm ((A))))))"
assumes v'199: "(\<forall>S_1 : ((((IsFiniteSet ((S_1)))) \<Rightarrow> (\<forall> pi \<in> ((Perm ((S_1)))) : (\<forall> k \<in> ((DOMAIN (pi))) : (\<forall> m \<in> ((DOMAIN (pi))) : (((((k) \<noteq> (m))) \<Rightarrow> (((fapply ((pi), (k))) \<noteq> (fapply ((pi), (m)))))))))))))"
shows "(\<forall> h \<in> ((DOMAIN (f))) : (\<forall> d \<in> ((DOMAIN (f))) : (((((h) \<noteq> (d))) \<Rightarrow> (((fapply ((f), (h))) \<noteq> (fapply ((f), (d)))))))))"(is "PROP ?ob'310")
proof -
ML_command {* writeln "*** TLAPS ENTER 310"; *}
show "PROP ?ob'310"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_d97c9c.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_d97c9c.znn.out
;; obligation #310
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "a_in" (TLA.in a (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))))
$hyp "b_in" (TLA.in b (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))))
$hyp "v'184" (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) a)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) b))
$hyp "v'196" (/\ (TLA.in A (TLA.SUBSET arith.Z))
(IsFiniteSet A))
$hyp "v'197" (= (TLA.DOMAIN f) (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)))
$hyp "v'198" (TLA.in f (Perm A))
$hyp "v'199" (A. ((S_1) (=> (IsFiniteSet S_1)
(TLA.bAll (Perm S_1) ((pi) (TLA.bAll (TLA.DOMAIN pi) ((k) (TLA.bAll (TLA.DOMAIN pi) ((m) (=> (-. (= k
m)) (-. (= (TLA.fapply pi k)
(TLA.fapply pi m)))))))))))))
$goal (TLA.bAll (TLA.DOMAIN f) ((h) (TLA.bAll (TLA.DOMAIN f) ((d) (=> (-. (= h
d)) (-. (= (TLA.fapply f h)
(TLA.fapply f d))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"((A \\in SUBSET(Int))&IsFiniteSet(A))" (is "?z_hn&?z_hr")
 using v'196 by blast
 have z_Hk:"(f \\in Perm(A))" (is "?z_hk")
 using v'198 by blast
 have z_Hl:"(\\A S_1:(IsFiniteSet(S_1)=>bAll(Perm(S_1), (\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m])))))))))))" (is "\\A x : ?z_hbn(x)")
 using v'199 by blast
 assume z_Hm:"(~bAll(DOMAIN(f), (\<lambda>h. bAll(DOMAIN(f), (\<lambda>d. ((h~=d)=>((f[h])~=(f[d]))))))))" (is "~?z_hbo")
 have z_Hr: "?z_hr"
 by (rule zenon_and_1 [OF z_Hi])
 have z_Hca: "?z_hbn(A)" (is "_=>?z_hcb")
 by (rule zenon_all_0 [of "?z_hbn" "A", OF z_Hl])
 show FALSE
 proof (rule zenon_imply [OF z_Hca])
  assume z_Hcc:"(~?z_hr)"
  show FALSE
  by (rule notE [OF z_Hcc z_Hr])
 next
  assume z_Hcb:"?z_hcb"
  have z_Hbo: "?z_hbo"
  by (rule zenon_all_in_0 [of "Perm(A)" "(\<lambda>pi. bAll(DOMAIN(pi), (\<lambda>k. bAll(DOMAIN(pi), (\<lambda>m. ((k~=m)=>((pi[k])~=(pi[m]))))))))", OF z_Hcb z_Hk])
  show FALSE
  by (rule notE [OF z_Hm z_Hbo])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 310"; *} qed
lemma ob'269:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
assumes v'182: "((\<And> a :: c. a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<Longrightarrow> (\<And> b :: c. b \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<Longrightarrow> ((((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (a))) = (fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]), (b))))) \<Longrightarrow> (((a) = (b)))))))"
assumes v'183: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]) \<in> ([((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<rightarrow> (((A) \<union> ({(s)})))])))"
assumes v'184: "((\<And> S_1 :: c. (\<And> T :: c. (\<And> F :: c. F \<in> ([(S_1) \<rightarrow> (T)]) \<Longrightarrow> ((\<forall> a \<in> (S_1) : (\<forall> b \<in> (S_1) : (((((fapply ((F), (a))) = (fapply ((F), (b))))) \<Rightarrow> (((a) = (b))))))) \<Longrightarrow> (((F) \<in> ((Injection ((S_1), (T)))))))))))"
shows "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (cond((((k) = ((Succ[0])))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))))]) \<in> ((Injection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"(is "PROP ?ob'269")
proof -
ML_command {* writeln "*** TLAPS ENTER 269"; *}
show "PROP ?ob'269"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_a1c711.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_a1c711.znn.out
;; obligation #269
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "v'182" (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((a) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((b) (=> (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) a)
(TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0))))))) b)) (= a
b))))))
$hyp "v'183" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))))))
(TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$hyp "v'184" (A. ((S_1) (A. ((T) (TLA.bAll (TLA.FuncSet S_1 T) ((F) (=> (TLA.bAll S_1 ((a) (TLA.bAll S_1 ((b) (=> (= (TLA.fapply F a)
(TLA.fapply F b)) (= a b)))))) (TLA.in F (Injection S_1
T)))))))))
$goal (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.cond (= k
(TLA.fapply TLA.Succ 0)) s (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))))))
(Injection (arith.intrange (TLA.fapply TLA.Succ 0) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"(\\A S_1:(\\A T:bAll(FuncSet(S_1, T), (\<lambda>F. (bAll(S_1, (\<lambda>a. bAll(S_1, (\<lambda>b. (((F[a])=(F[b]))=>(a=b))))))=>(F \\in Injection(S_1, T)))))))" (is "\\A x : ?z_hbe(x)")
 using v'184 by blast
 have z_Hf:"bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>b. (((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[a])=(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))[b]))=>(a=b))))))" (is "?z_hf")
 using v'182 by blast
 have z_Hg:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))) \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hg")
 using v'183 by blast
 assume z_Hi:"(~(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))) \\in Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))))" (is "~?z_hce")
 have z_Hcg: "?z_hbe(isa'dotdot(1, (Cardinality(A) + 1)))" (is "\\A x : ?z_hch(x)")
 by (rule zenon_all_0 [of "?z_hbe" "isa'dotdot(1, (Cardinality(A) + 1))", OF z_Hh])
 have z_Hci: "?z_hch((A \\cup {s}))" (is "?z_hci")
 by (rule zenon_all_0 [of "?z_hch" "(A \\cup {s})", OF z_Hcg])
 have z_Hcj_z_Hci: "(\\A x:((x \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))=>(bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. bAll(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>b. (((x[a])=(x[b]))=>(a=b))))))=>(x \\in Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))))) == ?z_hci" (is "?z_hcj == _")
 by (unfold bAll_def)
 have z_Hcj: "?z_hcj" (is "\\A x : ?z_hcx(x)")
 by (unfold z_Hcj_z_Hci, fact z_Hci)
 have z_Hcy: "?z_hcx(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))])))))" (is "_=>?z_hcz")
 by (rule zenon_all_0 [of "?z_hcx" "Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. cond((k=1), s, (f[(k +  -.(1))]))))", OF z_Hcj])
 show FALSE
 proof (rule zenon_imply [OF z_Hcy])
  assume z_Hda:"(~?z_hg)"
  show FALSE
  by (rule notE [OF z_Hda z_Hg])
 next
  assume z_Hcz:"?z_hcz"
  show FALSE
  proof (rule zenon_imply [OF z_Hcz])
   assume z_Hdb:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hdb z_Hf])
  next
   assume z_Hce:"?z_hce"
   show FALSE
   by (rule notE [OF z_Hi z_Hce])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 269"; *} qed
lemma ob'455:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'149: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'159: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'160: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((((Injection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))) \<inter> ((Surjection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))))"
fixes pred
assumes pred_in : "(pred \<in> (subsetOf((A), %z. ((less ((z), (s)))))))"
fixes a_predunde_ka
assumes a_predunde_ka_in : "(a_predunde_ka \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
assumes v'200: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]) \<in> ((Injection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"
assumes v'201: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]) \<in> ((Surjection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"
shows "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]) \<in> ((((Injection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)})))))) \<inter> ((Surjection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))))"(is "PROP ?ob'455")
proof -
ML_command {* writeln "*** TLAPS ENTER 455"; *}
show "PROP ?ob'455"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_dcf691.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_dcf691.znn.out
;; obligation #455
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'149" (IsFiniteSet S)
$hyp "v'159" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'160" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (TLA.cap (Injection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)) A) (Surjection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A)))
$hyp "pred_in" (TLA.in pred (TLA.subsetOf A ((z) (arith.lt z
s))))
$hyp "a_predunde_ka_in" (TLA.in a_predunde_ka (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)))
$hyp "v'200" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) )))
(Injection (arith.intrange (TLA.fapply TLA.Succ 0) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$hyp "v'201" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) )))
(Surjection (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$goal (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) )))
(TLA.cap (Injection (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A (TLA.set s)))
(Surjection (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))])))) \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hi")
 using v'201 by blast
 have z_Hh:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))])))) \\in Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hh")
 using v'200 by blast
 assume z_Hj:"(~(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))])))) \\in (Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})) \\cap Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))))" (is "~?z_hbm")
 show FALSE
 proof (rule zenon_notin_cap [of "Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))]))))" "Injection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))" "Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))", OF z_Hj])
  assume z_Hbo:"(~?z_hh)"
  show FALSE
  by (rule notE [OF z_Hbo z_Hh])
 next
  assume z_Hbp:"(~?z_hi)"
  show FALSE
  by (rule notE [OF z_Hbp z_Hi])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 455"; *} qed
lemma ob'435:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
fixes A
fixes s
assumes v'160: "(((((A) \<union> ({(s)}))) \<in> ((SUBSET (Int)))))"
assumes v'161: "((IsFiniteSet ((((A) \<union> ({(s)}))))))"
fixes f
assumes f_in : "(f \<in> ((Bijection (((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))), (A)))))"
fixes pred
assumes pred_in : "(pred \<in> (subsetOf((A), %z. ((less ((z), (s)))))))"
fixes a_predunde_ka
assumes a_predunde_ka_in : "(a_predunde_ka \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
assumes v'200: "((\<And> b :: c. b \<in> (((A) \<union> ({(s)}))) \<Longrightarrow> (\<exists> a \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) : (((fapply (([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]), (a))) = (b))))))"
assumes v'201: "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]) \<in> ([((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))) \<rightarrow> (((A) \<union> ({(s)})))])))"
assumes v'202: "((\<And> S_1 :: c. (\<And> T :: c. (\<And> F :: c. F \<in> ([(S_1) \<rightarrow> (T)]) \<Longrightarrow> ((\<forall> t \<in> (T) : (\<exists> s_1 \<in> (S_1) : (((fapply ((F), (s_1))) = (t))))) \<Longrightarrow> (((F) \<in> ((Surjection ((S_1), (T)))))))))))"
shows "((([ k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))  \<mapsto> (Case(<<(((k) \<in> ((isa_peri_peri_a (((Succ[0])), (a_predunde_ka)))))), (((k) = ((arith_add ((a_predunde_ka), ((Succ[0]))))))), (((k) \<in> ((isa_peri_peri_a (((arith_add ((a_predunde_ka), ((Succ[Succ[0]]))))), ((arith_add (((Cardinality ((A)))), ((Succ[0]))))))))))>>,<<(fapply ((f), (k))), (s), (fapply ((f), ((arith_add ((k), ((minus (((Succ[0]))))))))))>>))]) \<in> ((Surjection (((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((Succ[0])))))))), (((A) \<union> ({(s)}))))))))"(is "PROP ?ob'435")
proof -
ML_command {* writeln "*** TLAPS ENTER 435"; *}
show "PROP ?ob'435"

(* BEGIN ZENON INPUT
;; file=POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_905df4.znn; PATH='/Users/uguryavuz/.opam/easycrypt/bin:/opt/homebrew/Caskroom/miniconda/base/envs/py39/bin:/opt/homebrew/Caskroom/miniconda/base/condabin:/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:/System/Cryptexes/App/usr/bin:/usr/bin:/bin:/usr/sbin:/sbin:/Library/TeX/texbin:/usr/local/munki:/opt/X11/bin:/Library/Apple/usr/bin:/Applications/Wireshark.app/Contents/MacOS:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/local/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/bin:/var/run/com.apple.security.cryptexd/codex.system/bootstrap/usr/appleinternal/bin:/Users/uguryavuz/.cargo/bin:/Users/uguryavuz/.spicetify:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/bin:/Users/uguryavuz/Desktop/EasyUC/uc-dsl/testing:/Users/uguryavuz/go/bin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >POPL24_HerlihyWingQueuePrelude.tlaps/tlapm_905df4.znn.out
;; obligation #435
$hyp "S_in" (TLA.in S (TLA.SUBSET arith.Z))
$hyp "v'150" (IsFiniteSet S)
$hyp "v'160" (TLA.in (TLA.cup A (TLA.set s))
(TLA.SUBSET arith.Z))
$hyp "v'161" (IsFiniteSet (TLA.cup A
(TLA.set s)))
$hyp "f_in" (TLA.in f (Bijection (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A))
A))
$hyp "pred_in" (TLA.in pred (TLA.subsetOf A ((z) (arith.lt z
s))))
$hyp "a_predunde_ka_in" (TLA.in a_predunde_ka (arith.intrange (TLA.fapply TLA.Succ 0)
(Cardinality A)))
$hyp "v'200" (TLA.bAll (TLA.cup A
(TLA.set s)) ((b) (TLA.bEx (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0))) ((a) (= (TLA.fapply (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) ))) a)
b)))))
$hyp "v'201" (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) )))
(TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
$hyp "v'202" (A. ((S_1) (A. ((T) (TLA.bAll (TLA.FuncSet S_1 T) ((F) (=> (TLA.bAll T ((t) (TLA.bEx S_1 ((s_1) (= (TLA.fapply F s_1)
t))))) (TLA.in F (Surjection S_1
T)))))))))
$goal (TLA.in (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) ((k) (TLA.CASE (TLA.in k
(arith.intrange (TLA.fapply TLA.Succ 0) a_predunde_ka)) (TLA.fapply f k) (= k
(arith.add a_predunde_ka (TLA.fapply TLA.Succ 0))) s (TLA.in k
(arith.intrange (arith.add a_predunde_ka
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (arith.add (Cardinality A)
(TLA.fapply TLA.Succ 0)))) (TLA.fapply f (arith.add k
(arith.minus (TLA.fapply TLA.Succ 0)))) )))
(Surjection (arith.intrange (TLA.fapply TLA.Succ 0)
(arith.add (Cardinality A) (TLA.fapply TLA.Succ 0))) (TLA.cup A
(TLA.set s))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"(\\A S_1:(\\A T:bAll(FuncSet(S_1, T), (\<lambda>F. (bAll(T, (\<lambda>t. bEx(S_1, (\<lambda>s_1. ((F[s_1])=t)))))=>(F \\in Surjection(S_1, T)))))))" (is "\\A x : ?z_hbd(x)")
 using v'202 by blast
 have z_Hh:"bAll((A \\cup {s}), (\<lambda>b. bEx(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>a. ((Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))]))))[a])=b)))))" (is "?z_hh")
 using v'200 by blast
 have z_Hi:"(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))])))) \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))" (is "?z_hi")
 using v'201 by blast
 assume z_Hk:"(~(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))])))) \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s}))))" (is "~?z_hcm")
 have z_Hco: "?z_hbd(isa'dotdot(1, (Cardinality(A) + 1)))" (is "\\A x : ?z_hcp(x)")
 by (rule zenon_all_0 [of "?z_hbd" "isa'dotdot(1, (Cardinality(A) + 1))", OF z_Hj])
 have z_Hcq: "?z_hcp((A \\cup {s}))" (is "?z_hcq")
 by (rule zenon_all_0 [of "?z_hcp" "(A \\cup {s})", OF z_Hco])
 have z_Hcr_z_Hcq: "(\\A x:((x \\in FuncSet(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))=>(bAll((A \\cup {s}), (\<lambda>t. bEx(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>s_1. ((x[s_1])=t)))))=>(x \\in Surjection(isa'dotdot(1, (Cardinality(A) + 1)), (A \\cup {s})))))) == ?z_hcq" (is "?z_hcr == _")
 by (unfold bAll_def)
 have z_Hcr: "?z_hcr" (is "\\A x : ?z_hdd(x)")
 by (unfold z_Hcr_z_Hcq, fact z_Hcq)
 have z_Hde: "?z_hdd(Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))])))))" (is "_=>?z_hdf")
 by (rule zenon_all_0 [of "?z_hdd" "Fcn(isa'dotdot(1, (Cardinality(A) + 1)), (\<lambda>k. (CASE (k \\in isa'dotdot(1, a_predunde_ka)) -> (f[k]) [] (k=(a_predunde_ka + 1)) -> s [] (k \\in isa'dotdot((a_predunde_ka + 2), (Cardinality(A) + 1))) -> (f[(k +  -.(1))]))))", OF z_Hcr])
 show FALSE
 proof (rule zenon_imply [OF z_Hde])
  assume z_Hdg:"(~?z_hi)"
  show FALSE
  by (rule notE [OF z_Hdg z_Hi])
 next
  assume z_Hdf:"?z_hdf"
  show FALSE
  proof (rule zenon_imply [OF z_Hdf])
   assume z_Hdh:"(~?z_hh)"
   show FALSE
   by (rule notE [OF z_Hdh z_Hh])
  next
   assume z_Hcm:"?z_hcm"
   show FALSE
   by (rule notE [OF z_Hk z_Hcm])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 435"; *} qed
lemma ob'459:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
(* usable definition Restrict suppressed *)
(* usable definition Range suppressed *)
(* usable definition Inverse suppressed *)
(* usable definition Injection suppressed *)
(* usable definition Surjection suppressed *)
(* usable definition Bijection suppressed *)
(* usable definition ExistsInjection suppressed *)
(* usable definition ExistsSurjection suppressed *)
(* usable definition ExistsBijection suppressed *)
(* usable definition NatInductiveDefHypothesis suppressed *)
(* usable definition NatInductiveDefConclusion suppressed *)
(* usable definition FiniteNatInductiveDefHypothesis suppressed *)
(* usable definition FiniteNatInductiveDefConclusion suppressed *)
(* usable definition IsTransitivelyClosedOn suppressed *)
(* usable definition IsWellFoundedOn suppressed *)
(* usable definition SetLessThan suppressed *)
(* usable definition WFDefOn suppressed *)
(* usable definition OpDefinesFcn suppressed *)
(* usable definition WFInductiveDefines suppressed *)
(* usable definition WFInductiveUnique suppressed *)
(* usable definition TransitiveClosureOn suppressed *)
(* usable definition OpToRel suppressed *)
(* usable definition PreImage suppressed *)
(* usable definition LexPairOrdering suppressed *)
(* usable definition LexProductOrdering suppressed *)
(* usable definition FiniteSubsetsOf suppressed *)
(* usable definition StrictSubsetOrdering suppressed *)
(* usable definition Perm suppressed *)
(* usable definition Len suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'150: "((IsFiniteSet ((S))))"
(* usable definition P suppressed *)
assumes v'158: "((P (({}))))"
assumes v'159: "((\<And> A :: c. (\<And> s :: c. (((P ((A)))) \<Longrightarrow> ((((s) \<notin> (A))) \<Longrightarrow> ((P ((((A) \<union> ({(s)})))))))))))"
assumes v'160: "((\<And> S_1 :: c. (((IsFiniteSet ((S_1)))) \<Longrightarrow> (\<And> P_1 :: c => c. (((P_1 (({})))) \<Longrightarrow> (((\<And> T :: c. (\<And> x :: c. (((IsFiniteSet ((T)))) \<Longrightarrow> (((P_1 ((T)))) \<Longrightarrow> ((((x) \<notin> (T))) \<Longrightarrow> ((P_1 ((((T) \<union> ({(x)})))))))))))) \<Longrightarrow> ((P_1 ((S_1))))))))))"
shows "((P ((S))))"(is "PROP ?ob'459")
proof -
ML_command {* writeln "*** TLAPS ENTER 459"; *}
show "PROP ?ob'459"
using assms by blast
ML_command {* writeln "*** TLAPS EXIT 459"; *} qed
end
