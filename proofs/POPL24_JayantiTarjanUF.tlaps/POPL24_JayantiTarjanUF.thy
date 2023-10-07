(* automatically generated -- do not edit manually *)
theory POPL24_JayantiTarjanUF imports Constant Zenon begin
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

lemma ob'104:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition InvocationLines suppressed *)
(* usable definition Lines suppressed *)
(* usable definition NodeSet suppressed *)
(* usable definition PowerSetNodes suppressed *)
(* usable definition States suppressed *)
(* usable definition Rets suppressed *)
(* usable definition AtomConfigs suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU2 suppressed *)
(* usable definition AugU2 suppressed *)
(* usable definition U2 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidPar suppressed *)
(* usable definition Validx suppressed *)
(* usable definition Validy suppressed *)
(* usable definition Validu suppressed *)
(* usable definition Validv suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition Validpc suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'203: "(((S) \<noteq> ({})))"
assumes v'204: "((IsFiniteSet ((S))))"
(* usable definition Pred suppressed *)
assumes v'210: "((a_Preda (({}))))"
assumes v'211: "((\<And> T :: c. (\<And> X :: c. (((a_Preda ((T)))) \<Longrightarrow> ((((X) \<notin> (T))) \<Longrightarrow> ((a_Preda ((((T) \<union> ({(X)})))))))))))"
assumes v'212: "((\<And> S_1 :: c. (((IsFiniteSet ((S_1)))) \<Longrightarrow> (\<And> P :: c => c. (((P (({})))) \<Longrightarrow> (((\<And> T :: c. (\<And> x_1 :: c. (((IsFiniteSet ((T)))) \<Longrightarrow> (((P ((T)))) \<Longrightarrow> ((((x_1) \<notin> (T))) \<Longrightarrow> ((P ((((T) \<union> ({(x_1)})))))))))))) \<Longrightarrow> ((P ((S_1))))))))))"
shows "((a_Preda ((S))))"(is "PROP ?ob'104")
proof -
ML_command {* writeln "*** TLAPS ENTER 104"; *}
show "PROP ?ob'104"
using assms by blast
ML_command {* writeln "*** TLAPS EXIT 104"; *} qed
lemma ob'91:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition InvocationLines suppressed *)
(* usable definition Lines suppressed *)
(* usable definition NodeSet suppressed *)
(* usable definition PowerSetNodes suppressed *)
(* usable definition States suppressed *)
(* usable definition Rets suppressed *)
(* usable definition AtomConfigs suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU2 suppressed *)
(* usable definition AugU2 suppressed *)
(* usable definition U2 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidPar suppressed *)
(* usable definition Validx suppressed *)
(* usable definition Validy suppressed *)
(* usable definition Validu suppressed *)
(* usable definition Validv suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition Validpc suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
fixes S
assumes S_in : "(S \<in> ((SUBSET (Int))))"
assumes v'203: "(((S) \<noteq> ({})))"
assumes v'204: "((IsFiniteSet ((S))))"
fixes T
fixes X
assumes v'212: "(((((T) \<union> ({(X)}))) \<in> ((SUBSET (Int)))))"
assumes v'218: "(\<forall> Y \<in> (T) : ((leq ((Y), (X)))))"
shows "(\<exists> X_1 \<in> (((T) \<union> ({(X)}))) : (\<forall> Y \<in> (((T) \<union> ({(X)}))) : ((leq ((Y), (X_1))))))"(is "PROP ?ob'91")
proof -
ML_command {* writeln "*** TLAPS ENTER 91"; *}
show "PROP ?ob'91"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 91"; *} qed
lemma ob'430:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition NodeSet suppressed *)
(* usable definition PowerSetNodes suppressed *)
(* usable definition States suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU2 suppressed *)
(* usable definition AugU2 suppressed *)
(* usable definition U2 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Validx suppressed *)
(* usable definition Validy suppressed *)
(* usable definition Validv suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'215: "(((((Par) \<in> ([(NodeSet) \<rightarrow> (NodeSet)]))) & (Validx) & (Validy) & (((u) \<in> ([(ProcSet) \<rightarrow> (NodeSet)]))) & (Validv) & (Valida) & (Validb) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''F2''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''F6''))) \<Rightarrow> (((fapply ((fapply ((t), (''f''))), (p))) = (fapply ((u), (p))))))))) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'216: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'224: "(((cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F6'')]))), ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F3'')]))))) \<and> (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (States), ''f'' : ([(ProcSet) \<rightarrow> (((((NodeSet) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = ((Max ((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))))))]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'225: "(((fapply ((pc), (p))) = (''F2'')))"
assumes v'226: "((((a_ahash_primea :: c)) = ([(a) EXCEPT ![(p)] = (fapply ((Par), (fapply ((u), (p)))))])))"
assumes v'227: "((((a_Parhash_primea :: c)) = (Par)))"
assumes v'228: "((((a_xhash_primea :: c)) = (x)))"
assumes v'229: "((((a_yhash_primea :: c)) = (y)))"
assumes v'230: "((((a_uhash_primea :: c)) = (u)))"
assumes v'231: "((((a_vhash_primea :: c)) = (v)))"
assumes v'232: "((((a_bhash_primea :: c)) = (b)))"
fixes a_punde_1a
assumes a_punde_1a_in : "(a_punde_1a \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'248: "(((fapply (((a_pchash_primea :: c)), (a_punde_1a))) = (''F6'')))"
assumes v'254: "(((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p)))))"
assumes v'258: "((((((Par) \<in> ([(NodeSet) \<rightarrow> (NodeSet)]))) & (Validx) & (Validy) & (((u) \<in> ([(ProcSet) \<rightarrow> (NodeSet)]))) & (Validv) & (Valida) & (Validb) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) \<Longrightarrow> ((ParPointsUp) \<Longrightarrow> ((a_SigmaIsPartition1a) \<Longrightarrow> ((a_SigmaIsPartition2a) \<Longrightarrow> ((SigmaIsCoarse) \<Longrightarrow> ((SigmaIsFine) \<Longrightarrow> (\<And> w :: c. w \<in> (NodeSet) \<Longrightarrow> (\<And> t_1 :: c. t_1 \<in> (M) \<Longrightarrow> ((((w) = (fapply ((Par), (w))))) \<Longrightarrow> ((((Max ((fapply ((fapply ((t_1), (''sigma''))), (w)))))) = (w)))))))))))))"
shows "(((fapply (((a_uhash_primea :: c)), (p))) = ((Max ((fapply ((fapply ((t), (''sigma''))), (fapply (((a_uhash_primea :: c)), (p))))))))))"(is "PROP ?ob'430")
proof -
ML_command {* writeln "*** TLAPS ENTER 430"; *}
show "PROP ?ob'430"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 430"; *} qed
lemma ob'554:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition NodeSet suppressed *)
(* usable definition PowerSetNodes suppressed *)
(* usable definition States suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU2 suppressed *)
(* usable definition AugU2 suppressed *)
(* usable definition U2 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Validx suppressed *)
(* usable definition Validy suppressed *)
(* usable definition Validv suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'215: "(((((Par) \<in> ([(NodeSet) \<rightarrow> (NodeSet)]))) & (Validx) & (Validy) & (((u) \<in> ([(ProcSet) \<rightarrow> (NodeSet)]))) & (Validv) & (Valida) & (Validb) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U2''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U11''))) \<Rightarrow> (((fapply ((fapply ((t), (''f''))), (p))) = (ACK))))))) & (InvUEx) & (Linearizable))"
assumes v'216: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'224: "(((cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F6'')]))), ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F3'')]))))) \<and> (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (States), ''f'' : ([(ProcSet) \<rightarrow> (((((NodeSet) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = ((Max ((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))))))]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'225: "(((fapply ((pc), (p))) = (''F2'')))"
assumes v'226: "((((a_ahash_primea :: c)) = ([(a) EXCEPT ![(p)] = (fapply ((Par), (fapply ((u), (p)))))])))"
assumes v'227: "((((a_Parhash_primea :: c)) = (Par)))"
assumes v'228: "((((a_xhash_primea :: c)) = (x)))"
assumes v'229: "((((a_yhash_primea :: c)) = (y)))"
assumes v'230: "((((a_uhash_primea :: c)) = (u)))"
assumes v'231: "((((a_vhash_primea :: c)) = (v)))"
assumes v'232: "((((a_bhash_primea :: c)) = (b)))"
fixes a_punde_1a
assumes a_punde_1a_in : "(a_punde_1a \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'259: "(((fapply (((a_pchash_primea :: c)), (a_punde_1a))) = (''U11'')))"
assumes v'265: "(((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p)))))"
assumes v'269: "((((((Par) \<in> ([(NodeSet) \<rightarrow> (NodeSet)]))) & (Validx) & (Validy) & (((u) \<in> ([(ProcSet) \<rightarrow> (NodeSet)]))) & (Validv) & (Valida) & (Validb) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) \<Longrightarrow> ((ParPointsUp) \<Longrightarrow> ((a_SigmaIsPartition1a) \<Longrightarrow> ((a_SigmaIsPartition2a) \<Longrightarrow> ((SigmaIsCoarse) \<Longrightarrow> ((SigmaIsFine) \<Longrightarrow> (\<And> w :: c. w \<in> (NodeSet) \<Longrightarrow> (\<And> t_1 :: c. t_1 \<in> (M) \<Longrightarrow> ((((w) = (fapply ((Par), (w))))) \<Longrightarrow> ((((Max ((fapply ((fapply ((t_1), (''sigma''))), (w)))))) = (w)))))))))))))"
shows "(((fapply (((a_uhash_primea :: c)), (p))) = ((Max ((fapply ((fapply ((t), (''sigma''))), (fapply (((a_uhash_primea :: c)), (p))))))))))"(is "PROP ?ob'554")
proof -
ML_command {* writeln "*** TLAPS ENTER 554"; *}
show "PROP ?ob'554"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 554"; *} qed
lemma ob'1094:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition Validpc suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (Valida) & (Validb) & (Validpc) & (ValidP)) & (ParPointsUp) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((z) \<in> (fapply ((fapply ((t), (''sigma''))), (z))))))) & (\<forall> w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((((w) \<in> (fapply ((fapply ((t), (''sigma''))), (z))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (w))) = (fapply ((fapply ((t), (''sigma''))), (z)))))))))) & (\<forall> w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((((fapply ((Par), (w))) = (z))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (w))) = (fapply ((fapply ((t), (''sigma''))), (z)))))))))) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U2''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
assumes v'231: "((((N) \<in> (Nat))) & ((geq ((N), ((Succ[0]))))))"
fixes w
assumes w_in : "(w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))"
fixes z
assumes z_in : "(z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'235: "(((fapply (((a_Parhash_primea :: c)), (w))) = (z)))"
assumes v'242: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'247: "((greater ((fapply ((u), (p))), (fapply ((v), (p))))))"
assumes v'248: "(((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'1094")
proof -
ML_command {* writeln "*** TLAPS ENTER 1094"; *}
show "PROP ?ob'1094"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1094"; *} qed
lemma ob'1172:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition Validpc suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'207: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (Valida) & (Validb) & (Validpc) & (ValidP)) & (ParPointsUp) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((z) \<in> (fapply ((fapply ((t), (''sigma''))), (z))))))) & (\<forall> w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((((w) \<in> (fapply ((fapply ((t), (''sigma''))), (z))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (w))) = (fapply ((fapply ((t), (''sigma''))), (z)))))))))) & (\<forall> w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((((fapply ((Par), (w))) = (z))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (w))) = (fapply ((fapply ((t), (''sigma''))), (z)))))))))) & (\<forall> w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t \<in> (M) : (((((((((w) \<noteq> (z))) \<and> (((fapply ((Par), (w))) = (w))))) \<and> (((fapply ((Par), (z))) = (z))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (w))) \<noteq> (fapply ((fapply ((t), (''sigma''))), (z)))))))))) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U2''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'208: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'222: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'223: "(((fapply ((pc), (p))) = (''U2'')))"
assumes v'231: "((((N) \<in> (Nat))) & ((geq ((N), ((Succ[0]))))))"
fixes w
assumes w_in : "(w \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))"
fixes z
assumes z_in : "(z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'235: "(((w) \<noteq> (z)))"
assumes v'236: "(((fapply (((a_Parhash_primea :: c)), (w))) = (w)))"
assumes v'237: "(((fapply (((a_Parhash_primea :: c)), (z))) = (z)))"
assumes v'244: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'248: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
assumes v'249: "(((((a_Parhash_primea :: c)) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_xhash_primea :: c)) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_yhash_primea :: c)) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_uhash_primea :: c)) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((a_h5177f9702571ff81aa5efc8691e149a :: c)) & ((a_h20c646bf2e20d940777968f4e13de6a :: c)) & ((a_h050a7efd12fc0a3d0847aaf41f7068a :: c)) & ((a_hb9418ef710c4039ad83083f283d0e4a :: c)))"
assumes v'250: "((h87ebdd0e7ac0bfb824a7941450cb9e :: c))"
assumes v'251: "(\<forall> z_1 \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t_1 \<in> ((a_Mhash_primea :: c)) : (((z_1) \<in> (fapply ((fapply ((t_1), (''sigma''))), (z_1)))))))"
assumes v'252: "(\<forall> w_1 \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z_1 \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t_1 \<in> ((a_Mhash_primea :: c)) : (((((w_1) \<in> (fapply ((fapply ((t_1), (''sigma''))), (z_1))))) \<Rightarrow> (((fapply ((fapply ((t_1), (''sigma''))), (w_1))) = (fapply ((fapply ((t_1), (''sigma''))), (z_1))))))))))"
assumes v'253: "(\<forall> w_1 \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> z_1 \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<forall> t_1 \<in> ((a_Mhash_primea :: c)) : (((((fapply (((a_Parhash_primea :: c)), (w_1))) = (z_1))) \<Rightarrow> (((fapply ((fapply ((t_1), (''sigma''))), (w_1))) = (fapply ((fapply ((t_1), (''sigma''))), (z_1))))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'1172")
proof -
ML_command {* writeln "*** TLAPS ENTER 1172"; *}
show "PROP ?ob'1172"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1172"; *} qed
lemma ob'1420:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Validb suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'209: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (Validb) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''F3''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'210: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'224: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'225: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'238: "(((fapply ((pc), (q))) = (''F3'')))"
assumes v'245: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'249: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'1420")
proof -
ML_command {* writeln "*** TLAPS ENTER 1420"; *}
show "PROP ?ob'1420"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1420"; *} qed
lemma ob'1468:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((b) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''F4''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((b), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'238: "(((fapply ((pc), (q))) = (''F4'')))"
assumes v'245: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'249: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'1468")
proof -
ML_command {* writeln "*** TLAPS ENTER 1468"; *}
show "PROP ?ob'1468"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1468"; *} qed
lemma ob'1530:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((b) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''F5''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((b), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'239: "(((fapply ((pc), (q))) = (''F5'')))"
assumes v'246: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'250: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'1530")
proof -
ML_command {* writeln "*** TLAPS ENTER 1530"; *}
show "PROP ?ob'1530"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1530"; *} qed
lemma ob'1984:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((b) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U5''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((b), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'245: "(((fapply ((pc), (q))) = (''U5'')))"
assumes v'252: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'256: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'1984")
proof -
ML_command {* writeln "*** TLAPS ENTER 1984"; *}
show "PROP ?ob'1984"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1984"; *} qed
lemma ob'2182:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((b) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U6''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((b), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'246: "(((fapply ((pc), (q))) = (''U6'')))"
assumes v'253: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'257: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'2182")
proof -
ML_command {* writeln "*** TLAPS ENTER 2182"; *}
show "PROP ?ob'2182"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 2182"; *} qed
lemma ob'2459:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Validb suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'209: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (Validb) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U8''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU9a) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'210: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'224: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'225: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'249: "(((fapply ((pc), (q))) = (''U8'')))"
assumes v'256: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'260: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'2459")
proof -
ML_command {* writeln "*** TLAPS ENTER 2459"; *}
show "PROP ?ob'2459"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 2459"; *} qed
lemma ob'2609:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((b) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U9''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((b), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU10a) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'249: "(((fapply ((pc), (q))) = (''U9'')))"
assumes v'256: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'260: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'2609")
proof -
ML_command {* writeln "*** TLAPS ENTER 2609"; *}
show "PROP ?ob'2609"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 2609"; *} qed
lemma ob'2800:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition Lines suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidP suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
assumes v'208: "(((((Par) \<in> ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((y) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((u) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((b) \<in> ([(ProcSet) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((pc) \<in> ([(ProcSet) \<rightarrow> (Lines)]))) & (ValidP)) & (ParPointsUp) & (a_SigmaIsPartition1a) & (a_SigmaIsPartition2a) & (SigmaIsCoarse) & (SigmaIsFine) & (a_InvF1a) & (a_InvF2a) & (a_InvF3a) & (a_InvF4a) & (a_InvF5a) & (a_InvF6a) & (InvFEx) & (a_InvU1a) & (a_InvU2a) & (a_InvU3a) & (a_InvU4a) & (a_InvU5a) & (a_InvU6a) & (a_InvU7a) & (a_InvU8a) & (a_InvU9a) & (\<forall> p \<in> (ProcSet) : (\<forall> t \<in> (M) : (((((fapply ((pc), (p))) = (''U10''))) \<Rightarrow> ((((fapply ((fapply ((t), (''sigma''))), (fapply ((u), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((x), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((v), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((a), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''sigma''))), (fapply ((b), (p))))) = (fapply ((fapply ((t), (''sigma''))), (fapply ((y), (p))))))) & (((fapply ((fapply ((t), (''f''))), (p))) = (NIL)))))))) & (a_InvU11a) & (InvUEx) & (Linearizable))"
assumes v'209: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'223: "(((CaseOther(<<(((fapply ((u), (p))) = (fapply ((v), (p))))), ((less ((fapply ((u), (p))), (fapply ((v), (p))))))>>,<<(((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_Parhash_primea :: c)) = (Par))) & ((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (cond((((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((u), (p)))] = (fapply ((v), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b)))))))>>,(cond((((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))), (((((a_Parhash_primea :: c)) = ([(Par) EXCEPT ![(fapply ((v), (p)))] = (fapply ((u), (p)))]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U11'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))), (((((a_Parhash_primea :: c)) = (Par))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U3'')]))) & (((((a_xhash_primea :: c)) = (x))) & ((((a_yhash_primea :: c)) = (y))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_ahash_primea :: c)) = (a))) & ((((a_bhash_primea :: c)) = (b))))))))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((SUBSET ((isa_peri_peri_a (((Succ[0])), (N))))))]), ''f'' : ([(ProcSet) \<rightarrow> ((((((isa_peri_peri_a (((Succ[0])), (N)))) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'224: "(((fapply ((pc), (p))) = (''U2'')))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'250: "(((fapply ((pc), (q))) = (''U10'')))"
assumes v'257: "(((fapply ((u), (p))) \<noteq> (fapply ((v), (p)))))"
assumes v'261: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> a_zunde_1a \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_zunde_1a) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (a_zunde_1a))) = (fapply ((fapply ((told), (''sigma''))), (a_zunde_1a)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'2800")
proof -
ML_command {* writeln "*** TLAPS ENTER 2800"; *}
show "PROP ?ob'2800"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 2800"; *} qed
lemma ob'3683:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition InvocationLines suppressed *)
(* usable definition Lines suppressed *)
(* usable definition NodeSet suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU2 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidPar suppressed *)
(* usable definition Validx suppressed *)
(* usable definition Validy suppressed *)
(* usable definition Validu suppressed *)
(* usable definition Validv suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition Validpc suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition I suppressed *)
assumes v'224: "(\<forall> s \<in> (M) : (\<forall> t \<in> (M) : (((s) = (t)))))"
assumes v'225: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'239: "((((a_LineU2a ((p)))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([(NodeSet) \<rightarrow> ((SUBSET (NodeSet)))]), ''f'' : ([(ProcSet) \<rightarrow> (((((NodeSet) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([(NodeSet) \<rightarrow> ((SUBSET (NodeSet)))]), ''f'' : ([(ProcSet) \<rightarrow> (((((NodeSet) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> (NodeSet) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> (NodeSet) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'240: "(((((I) \<and> (((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars))))))) \<Rightarrow> ((a_h9418e403c4596b7e1fe4f033af0015a :: c))))"
fixes s
assumes s_in : "(s \<in> ((a_Mhash_primea :: c)))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'249: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
fixes sold
assumes sold_in : "(sold \<in> (M))"
shows "(\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> (NodeSet) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> (NodeSet) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'3683")
proof -
ML_command {* writeln "*** TLAPS ENTER 3683"; *}
show "PROP ?ob'3683"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 3683"; *} qed
lemma ob'3682:
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
fixes ProcSet
fixes N
fixes NIL
fixes ACK
fixes Par Par'
fixes x x'
fixes y y'
fixes u u'
fixes v v'
fixes a a'
fixes b b'
fixes pc pc'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition augs suppressed *)
(* usable definition allvars suppressed *)
(* usable definition InvocationLines suppressed *)
(* usable definition Lines suppressed *)
(* usable definition NodeSet suppressed *)
(* usable definition Max suppressed *)
(* usable definition InitVars suppressed *)
(* usable definition sigmaInit suppressed *)
(* usable definition fInit suppressed *)
(* usable definition InitAug suppressed *)
(* usable definition Init suppressed *)
(* usable definition LineF1 suppressed *)
(* usable definition AugF1 suppressed *)
(* usable definition F1 suppressed *)
(* usable definition LineF2 suppressed *)
(* usable definition AugF2 suppressed *)
(* usable definition F2 suppressed *)
(* usable definition LineF3 suppressed *)
(* usable definition AugF3 suppressed *)
(* usable definition F3 suppressed *)
(* usable definition LineF4 suppressed *)
(* usable definition AugF4 suppressed *)
(* usable definition F4 suppressed *)
(* usable definition LineF5 suppressed *)
(* usable definition AugF5 suppressed *)
(* usable definition F5 suppressed *)
(* usable definition LineF6 suppressed *)
(* usable definition AugF6 suppressed *)
(* usable definition F6 suppressed *)
(* usable definition LineU1 suppressed *)
(* usable definition AugU1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition LineU2 suppressed *)
(* usable definition LineU3 suppressed *)
(* usable definition AugU3 suppressed *)
(* usable definition U3 suppressed *)
(* usable definition LineU4 suppressed *)
(* usable definition AugU4 suppressed *)
(* usable definition U4 suppressed *)
(* usable definition LineU5 suppressed *)
(* usable definition AugU5 suppressed *)
(* usable definition U5 suppressed *)
(* usable definition LineU6 suppressed *)
(* usable definition AugU6 suppressed *)
(* usable definition U6 suppressed *)
(* usable definition LineU7 suppressed *)
(* usable definition AugU7 suppressed *)
(* usable definition U7 suppressed *)
(* usable definition LineU8 suppressed *)
(* usable definition AugU8 suppressed *)
(* usable definition U8 suppressed *)
(* usable definition LineU9 suppressed *)
(* usable definition AugU9 suppressed *)
(* usable definition U9 suppressed *)
(* usable definition LineU10 suppressed *)
(* usable definition AugU10 suppressed *)
(* usable definition U10 suppressed *)
(* usable definition LineU11 suppressed *)
(* usable definition AugU11 suppressed *)
(* usable definition U11 suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ValidPar suppressed *)
(* usable definition Validx suppressed *)
(* usable definition Validy suppressed *)
(* usable definition Validu suppressed *)
(* usable definition Validv suppressed *)
(* usable definition Valida suppressed *)
(* usable definition Validb suppressed *)
(* usable definition Validpc suppressed *)
(* usable definition ParPointsUp suppressed *)
(* usable definition SigmaIsPartition1 suppressed *)
(* usable definition SigmaIsPartition2 suppressed *)
(* usable definition SigmaIsCoarse suppressed *)
(* usable definition SigmaIsFine suppressed *)
(* usable definition InvF1 suppressed *)
(* usable definition InvF2 suppressed *)
(* usable definition InvF3 suppressed *)
(* usable definition InvF4 suppressed *)
(* usable definition InvF5 suppressed *)
(* usable definition InvF6 suppressed *)
(* usable definition InvFEx suppressed *)
(* usable definition InvU1 suppressed *)
(* usable definition InvU2 suppressed *)
(* usable definition InvU3 suppressed *)
(* usable definition InvU4 suppressed *)
(* usable definition InvU5 suppressed *)
(* usable definition InvU6 suppressed *)
(* usable definition InvU7 suppressed *)
(* usable definition InvU8 suppressed *)
(* usable definition InvU9 suppressed *)
(* usable definition InvU10 suppressed *)
(* usable definition InvU11 suppressed *)
(* usable definition InvUEx suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition I suppressed *)
assumes v'224: "(\<forall> s \<in> (M) : (\<forall> t \<in> (M) : (((s) = (t)))))"
assumes v'225: "(((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars)))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'239: "((((a_LineU2a ((p)))) \<and> (cond((((fapply ((u), (p))) = (fapply ((v), (p))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([(NodeSet) \<rightarrow> ((SUBSET (NodeSet)))]), ''f'' : ([(ProcSet) \<rightarrow> (((((NodeSet) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), (cond(((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p))))))))), ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : ([(NodeSet) \<rightarrow> ((SUBSET (NodeSet)))]), ''f'' : ([(ProcSet) \<rightarrow> (((((NodeSet) \<union> ({(NIL)}))) \<union> ({(ACK)})))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> (NodeSet) : (((((z) \<in> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> (NodeSet) : (((((z) \<notin> (((fapply ((fapply ((told), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((told), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((t), (''sigma''))), (z))) = (fapply ((fapply ((told), (''sigma''))), (z)))))))) & (((fapply ((t), (''f''))) = ([(fapply ((told), (''f''))) EXCEPT ![(p)] = (ACK)]))))))))), ((((a_Mhash_primea :: c)) = (M)))))))))"
assumes v'240: "(((((I) \<and> (((Next) \<or> ((((h1f94a75a8ae74b67a209ddb511649b :: c)) = (allvars))))))) \<Rightarrow> ((a_h9418e403c4596b7e1fe4f033af0015a :: c))))"
fixes s
assumes s_in : "(s \<in> ((a_Mhash_primea :: c)))"
fixes t
assumes t_in : "(t \<in> ((a_Mhash_primea :: c)))"
assumes v'249: "((((((less ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((u), (p))))) = (fapply ((u), (p))))))) \<or> ((((greater ((fapply ((u), (p))), (fapply ((v), (p)))))) \<and> (((fapply ((Par), (fapply ((v), (p))))) = (fapply ((v), (p)))))))))"
shows "(\<exists> sold \<in> (M) : ((((fapply ((fapply ((sold), (''f''))), (p))) = (NIL))) & (\<forall> z \<in> (NodeSet) : (((((z) \<in> (((fapply ((fapply ((sold), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((sold), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((s), (''sigma''))), (z))) = (((fapply ((fapply ((sold), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((sold), (''sigma''))), (fapply ((y), (p)))))))))))) & (\<forall> z \<in> (NodeSet) : (((((z) \<notin> (((fapply ((fapply ((sold), (''sigma''))), (fapply ((x), (p))))) \<union> (fapply ((fapply ((sold), (''sigma''))), (fapply ((y), (p))))))))) \<Rightarrow> (((fapply ((fapply ((s), (''sigma''))), (z))) = (fapply ((fapply ((sold), (''sigma''))), (z)))))))) & (((fapply ((s), (''f''))) = ([(fapply ((sold), (''f''))) EXCEPT ![(p)] = (ACK)])))))"(is "PROP ?ob'3682")
proof -
ML_command {* writeln "*** TLAPS ENTER 3682"; *}
show "PROP ?ob'3682"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 3682"; *} qed
end
