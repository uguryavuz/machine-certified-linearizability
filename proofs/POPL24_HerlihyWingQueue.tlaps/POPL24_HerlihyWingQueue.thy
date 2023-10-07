(* automatically generated -- do not edit manually *)
theory POPL24_HerlihyWingQueue imports Constant Zenon begin
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

lemma ob'951:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E1 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'231: "(cond((((fapply ((Q), (fapply ((j), (p))))) = (BOT))), (cond((((fapply ((j), (p))) = ((arith_add ((fapply ((l), (p))), ((minus (((Succ[0])))))))))), (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''D1'')]))) & (((((a_jhash_primea :: c)) = (j))) & ((((a_Mhash_primea :: c)) = (M))))), (((((a_jhash_primea :: c)) = ([(j) EXCEPT ![(p)] = ((arith_add ((fapply ((j), (p))), ((Succ[0])))))]))) & (((((a_pchash_primea :: c)) = (pc))) & ((((a_Mhash_primea :: c)) = (M))))))), (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''D4'')]))) & ((((a_jhash_primea :: c)) = (j))) & ((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %d. (((a_h022c5783954683bdcbcacced356fd6a ((d)) :: c)) & (\<exists> a_ca \<in> (M) : ((((fapply ((fapply ((d), (''fres''))), (p))) = ((Head ((fapply ((a_ca), (''sigma'')))))))) & (\<forall> q \<in> (ProcSet) : (((((q) \<noteq> (p))) \<Rightarrow> (((fapply ((fapply ((d), (''fres''))), (q))) = (fapply ((fapply ((a_ca), (''fres''))), (q)))))))) & (((fapply ((d), (''sigma''))) = ((Tail ((fapply ((a_ca), (''sigma''))))))))))))))))))"
assumes v'232: "(((fapply ((pc), (p))) = (''D3'')))"
assumes v'233: "((((a_xhash_primea :: c)) = ([(x) EXCEPT ![(p)] = (fapply ((Q), (fapply ((j), (p)))))])))"
assumes v'234: "((((a_Qhash_primea :: c)) = ([(Q) EXCEPT ![(fapply ((j), (p)))] = (BOT)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = (X)))"
assumes v'236: "((((a_ihash_primea :: c)) = (i)))"
assumes v'237: "((((a_lhash_primea :: c)) = (l)))"
assumes v'238: "((((a_vhash_primea :: c)) = (v)))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'241: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'242: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'251: "(((fapply ((Q), (fapply ((j), (p))))) \<noteq> (BOT)))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
assumes v'284: "(((fapply ((((''sigma'' :> ((Tail ((fapply ((a_ca), (''sigma''))))))) @@ (''fres'' :> ([(fapply ((a_ca), (''fres''))) EXCEPT ![(p)] = ((Head ((fapply ((a_ca), (''sigma''))))))])))), (''sigma''))) \<in> ([((DOMAIN (seq))) \<rightarrow> (((Nat) \\ ({((0))})))])))"
assumes v'285: "((([ k \<in> ((DOMAIN (seq)))  \<mapsto> (CaseOther(<<(((fapply (((a_Qhash_primea :: c)), (fapply ((seq), (k))))) \<noteq> (BOT)))>>,<<(fapply (((a_Qhash_primea :: c)), (fapply ((seq), (k)))))>>,(fapply (((a_vhash_primea :: c)), (bChoice((ProcSet), %r. (((((fapply (((a_pchash_primea :: c)), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply ((seq), (k)))))))))))))]) \<in> ([((DOMAIN (seq))) \<rightarrow> (((Nat) \\ ({((0))})))])))"
assumes v'286: "(\<forall> k \<in> ((DOMAIN (seq))) : (((fapply ((fapply ((((''sigma'' :> ((Tail ((fapply ((a_ca), (''sigma''))))))) @@ (''fres'' :> ([(fapply ((a_ca), (''fres''))) EXCEPT ![(p)] = ((Head ((fapply ((a_ca), (''sigma''))))))])))), (''sigma''))), (k))) = (fapply (([ k_1 \<in> ((DOMAIN (seq)))  \<mapsto> (CaseOther(<<(((fapply (((a_Qhash_primea :: c)), (fapply ((seq), (k_1))))) \<noteq> (BOT)))>>,<<(fapply (((a_Qhash_primea :: c)), (fapply ((seq), (k_1)))))>>,(fapply (((a_vhash_primea :: c)), (bChoice((ProcSet), %r. (((((fapply (((a_pchash_primea :: c)), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply ((seq), (k_1)))))))))))))]), (k))))))"
shows "(((fapply ((((''sigma'' :> ((Tail ((fapply ((a_ca), (''sigma''))))))) @@ (''fres'' :> ([(fapply ((a_ca), (''fres''))) EXCEPT ![(p)] = ((Head ((fapply ((a_ca), (''sigma''))))))])))), (''sigma''))) = ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (CaseOther(<<(((fapply (((a_Qhash_primea :: c)), (fapply ((seq), (k))))) \<noteq> (BOT)))>>,<<(fapply (((a_Qhash_primea :: c)), (fapply ((seq), (k)))))>>,(fapply (((a_vhash_primea :: c)), (bChoice((ProcSet), %q. (((((fapply (((a_pchash_primea :: c)), (q))) = (''E2''))) \<and> (((fapply (((a_ihash_primea :: c)), (q))) = (fapply ((seq), (k)))))))))))))])))"(is "PROP ?ob'951")
proof -
ML_command {* writeln "*** TLAPS ENTER 951"; *}
show "PROP ?ob'951"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 951"; *} qed
lemma ob'1221:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'204: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'210: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'233: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'234: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'235: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'236: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'237: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'238: "((((a_jhash_primea :: c)) = (j)))"
assumes v'239: "((((a_lhash_primea :: c)) = (l)))"
assumes v'240: "((((a_xhash_primea :: c)) = (x)))"
assumes v'241: "((((a_vhash_primea :: c)) = (v)))"
assumes v'242: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> ((Perm ((S)))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'245: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'246: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'254: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
assumes v'266: "(\<exists> z \<in> ((isa_peri_peri_a (((arith_add ((k), ((Succ[0]))))), ((Cardinality ((A))))))) : (((fapply ((Q), (fapply ((seq), (z))))) \<noteq> (BOT))))"
fixes z
assumes z_in : "(z \<in> ((isa_peri_peri_a (((arith_add ((k), ((Succ[0]))))), ((Cardinality ((A))))))))"
assumes v'282: "(((fapply ((seq), (z))) \<in> (A)))"
assumes v'283: "(\<forall> b \<in> (A) : ((leq ((b), (X)))))"
shows "((leq ((fapply ((seq), (z))), (X))))"(is "PROP ?ob'1221")
proof -
ML_command {* writeln "*** TLAPS ENTER 1221"; *}
show "PROP ?ob'1221"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1221"; *} qed
lemma ob'1212:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'204: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'210: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'233: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'234: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'235: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'236: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'237: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'238: "((((a_jhash_primea :: c)) = (j)))"
assumes v'239: "((((a_lhash_primea :: c)) = (l)))"
assumes v'240: "((((a_xhash_primea :: c)) = (x)))"
assumes v'241: "((((a_vhash_primea :: c)) = (v)))"
assumes v'242: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> ((Perm ((S)))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'245: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'246: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'254: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
assumes v'266: "(\<exists> z \<in> ((isa_peri_peri_a (((arith_add ((k), ((Succ[0]))))), ((Cardinality ((A))))))) : (((fapply ((Q), (fapply ((seq), (z))))) \<noteq> (BOT))))"
fixes z
assumes z_in : "(z \<in> ((isa_peri_peri_a (((arith_add ((k), ((Succ[0]))))), ((Cardinality ((A))))))))"
assumes v'286: "((leq ((fapply ((seq), (z))), (X))))"
assumes v'287: "(((fapply ((seq), (k))) \<noteq> (fapply ((seq), (z)))))"
assumes v'288: "(((X) = (fapply ((seq), (k)))))"
shows "((less ((fapply ((seq), (z))), (fapply ((seq), (k))))))"(is "PROP ?ob'1212")
proof -
ML_command {* writeln "*** TLAPS ENTER 1212"; *}
show "PROP ?ob'1212"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1212"; *} qed
lemma ob'1195:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "(((((((pc) \<in> ([(ProcSet) \<rightarrow> ({(''L0''), (''E1''), (''E2''), (''E3''), (''D1''), (''D2''), (''D3''), (''D4'')})]))) & (((X) \<in> (((Nat) \\ ({((0))}))))) & (((Q) \<in> ([(((Nat) \\ ({((0))}))) \<rightarrow> (((((Nat) \\ ({((0))}))) \<union> ({(BOT)})))]))) & (((i) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((j) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((l) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> (((((Nat) \\ ({((0))}))) \<union> ({(BOT)})))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((M) \<in> ((SUBSET (subsetOf((CDomain), %a_ca. ((CFTypeOK ((a_ca))))))))))) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> ((Perm ((S)))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'244: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
assumes v'258: "((IsFiniteSet (((isa_peri_peri_a (((Succ[0])), (X)))))))"
assumes v'259: "((\<And> S :: c. (((IsFiniteSet ((S)))) \<Longrightarrow> (\<And> T :: c. T \<in> ((SUBSET (S))) \<Longrightarrow> (((IsFiniteSet ((T)))) & ((leq (((Cardinality ((T)))), ((Cardinality ((S))))))) & ((((((Cardinality ((S)))) = ((Cardinality ((T)))))) \<Rightarrow> (((S) = (T))))))))))"
shows "((IsFiniteSet ((A))))"(is "PROP ?ob'1195")
proof -
ML_command {* writeln "*** TLAPS ENTER 1195"; *}
show "PROP ?ob'1195"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1195"; *} qed
lemma ob'1303:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \<rightarrow> (S)]), %f. (\<forall> w \<in> (S) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (((fapply ((f), (q))) = (w))))))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) \<rightarrow> (A)]), %f. (\<forall> w \<in> (A) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((f), (q))) = (w))))))))"
assumes v'244: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes m
assumes m_in : "(m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((X), ((minus (((Succ[0]))))))))))))"
assumes v'273: "(((m) \<in> (setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z)))))))"
assumes v'274: "(((fapply ((Q), (m))) = (BOT)))"
shows "(\<exists> km \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))) : (((fapply ((seq), (km))) = (m))))"(is "PROP ?ob'1303")
proof -
ML_command {* writeln "*** TLAPS ENTER 1303"; *}
show "PROP ?ob'1303"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1303"; *} qed
lemma ob'1293:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \<rightarrow> (S)]), %f. (\<forall> w \<in> (S) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (((fapply ((f), (q))) = (w))))))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) \<rightarrow> (A)]), %f. (\<forall> w \<in> (A) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((f), (q))) = (w))))))))"
assumes v'244: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes m
assumes m_in : "(m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((X), ((minus (((Succ[0]))))))))))))"
assumes v'272: "(((fapply ((Q), (m))) \<noteq> (BOT)))"
assumes v'277: "(((m) \<in> (A)))"
shows "(\<exists> km \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((seq), (km))) = (m))))"(is "PROP ?ob'1293")
proof -
ML_command {* writeln "*** TLAPS ENTER 1293"; *}
show "PROP ?ob'1293"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1293"; *} qed
lemma ob'1259:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \<rightarrow> (S)]), %f. (\<forall> w \<in> (S) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (((fapply ((f), (q))) = (w))))))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) \<rightarrow> (A)]), %f. (\<forall> w \<in> (A) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((f), (q))) = (w))))))))"
assumes v'244: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
assumes v'267: "((((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))]))) = ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))))"
assumes v'268: "((((Cardinality ((setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z)))))))) = ((arith_add ((k), ((minus (((Succ[0]))))))))))"
shows "((([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))]) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z))))))))))) \<rightarrow> (setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z)))))]), %f. (\<forall> w \<in> (setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z))))) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z))))))))))) : (((fapply ((f), (q))) = (w)))))))))"(is "PROP ?ob'1259")
proof -
ML_command {* writeln "*** TLAPS ENTER 1259"; *}
show "PROP ?ob'1259"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1259"; *} qed
lemma ob'1312:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'204: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'210: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'233: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'234: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'235: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'236: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'237: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'238: "((((a_jhash_primea :: c)) = (j)))"
assumes v'239: "((((a_lhash_primea :: c)) = (l)))"
assumes v'240: "((((a_xhash_primea :: c)) = (x)))"
assumes v'241: "((((a_vhash_primea :: c)) = (v)))"
assumes v'242: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> ((Perm ((S)))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'245: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'246: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'254: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes m
assumes m_in : "(m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((X), ((minus (((Succ[0]))))))))))))"
assumes v'274: "(((m) \<in> (setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z)))))))"
assumes v'275: "(((fapply ((Q), (m))) = (BOT)))"
fixes km
assumes km_in : "(km \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))))"
assumes v'285: "(((fapply ((seq), (km))) = (m)))"
assumes v'286: "(\<forall> y \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))) : (((y) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))))"
assumes v'287: "(((((km) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))) \<Rightarrow> (((fapply ((seq), (km))) \<in> (A)))))"
shows "(((m) \<in> (A)))"(is "PROP ?ob'1312")
proof -
ML_command {* writeln "*** TLAPS ENTER 1312"; *}
show "PROP ?ob'1312"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1312"; *} qed
lemma ob'1309:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \<rightarrow> (S)]), %f. (\<forall> w \<in> (S) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (((fapply ((f), (q))) = (w))))))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) \<rightarrow> (A)]), %f. (\<forall> w \<in> (A) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((f), (q))) = (w))))))))"
assumes v'244: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes m
assumes m_in : "(m \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((X), ((minus (((Succ[0]))))))))))))"
assumes v'273: "(((m) \<in> (setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z)))))))"
assumes v'274: "(((fapply ((Q), (m))) = (BOT)))"
fixes km
assumes km_in : "(km \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))))"
assumes v'283: "(((fapply ((seq), (km))) = (m)))"
shows "(((((km) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))) \<Rightarrow> (((fapply ((seq), (km))) \<in> (A)))))"(is "PROP ?ob'1309")
proof -
ML_command {* writeln "*** TLAPS ENTER 1309"; *}
show "PROP ?ob'1309"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1309"; *} qed
lemma ob'1372:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) \<rightarrow> (S)]), %f. (\<forall> w \<in> (S) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((S))))))) : (((fapply ((f), (q))) = (w))))))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) \<rightarrow> (A)]), %f. (\<forall> w \<in> (A) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((f), (q))) = (w))))))))"
assumes v'244: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes n
assumes n_in : "(n \<in> (setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z))))))"
fixes kn
assumes kn_in : "(kn \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))))"
assumes v'279: "(((fapply ((seq), (kn))) = (n)))"
assumes v'280: "(\<forall> y \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))) : (((y) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))))"
shows "(((kn) \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A)))))))))"(is "PROP ?ob'1372")
proof -
ML_command {* writeln "*** TLAPS ENTER 1372"; *}
show "PROP ?ob'1372"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1372"; *} qed
lemma ob'1439:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
assumes v'232: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'233: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'234: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'235: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'236: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'237: "((((a_jhash_primea :: c)) = (j)))"
assumes v'238: "((((a_lhash_primea :: c)) = (l)))"
assumes v'239: "((((a_xhash_primea :: c)) = (x)))"
assumes v'240: "((((a_vhash_primea :: c)) = (v)))"
assumes v'241: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq \<in> ((Perm ((S)))) : ((((fapply ((a_ca), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k \<in> ((DOMAIN (seq)))  \<mapsto> (fapply ((v), (fapply ((seq), (k)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'244: "(\<forall> k \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))) : ((((((fapply (((a_Qhash_primea :: c)), (k))) \<noteq> (BOT))) \<Rightarrow> (((k) \<in> (A))))) & (((((((k) \<in> (A))) \<and> (((fapply (((a_Qhash_primea :: c)), (k))) = (BOT))))) \<Rightarrow> (\<exists> q \<in> (ProcSet) : (((((fapply (((a_pchash_primea :: c)), (q))) = (''E2''))) \<and> (((fapply (((a_ihash_primea :: c)), (q))) = (k))))))))))"
assumes v'245: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'253: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
fixes z
assumes z_in : "(z \<in> ((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]))))"
assumes v'282: "(((fapply ((Q), (fapply ((seq), ((arith_add ((z), ((arith_add ((k), ((minus (((Succ[0]))))))))))))))) = (BOT)))"
assumes v'283: "(((fapply ((seq), ((arith_add ((z), ((arith_add ((k), ((minus (((Succ[0]))))))))))))) \<in> (A)))"
shows "(\<exists> r \<in> (ProcSet) : (((((fapply (((a_pchash_primea :: c)), (r))) = (''E2''))) \<and> (((fapply (((a_ihash_primea :: c)), (r))) = (fapply ((seq), ((arith_add ((z), ((arith_add ((k), ((minus (((Succ[0]))))))))))))))))))"(is "PROP ?ob'1439")
proof -
ML_command {* writeln "*** TLAPS ENTER 1439"; *}
show "PROP ?ob'1439"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1439"; *} qed
lemma ob'1890:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "(((((((pc) \<in> ([(ProcSet) \<rightarrow> ({(''L0''), (''E1''), (''E2''), (''E3''), (''D1''), (''D2''), (''D3''), (''D4'')})]))) & (((X) \<in> (((Nat) \\ ({((0))}))))) & (((Q) \<in> ([(((Nat) \\ ({((0))}))) \<rightarrow> (((((Nat) \\ ({((0))}))) \<union> ({(BOT)})))]))) & (((i) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((j) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((l) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> (((((Nat) \\ ({((0))}))) \<union> ({(BOT)})))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((M) \<in> ((SUBSET (subsetOf((CDomain), %a_ca. ((CFTypeOK ((a_ca))))))))))) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'235: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'236: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'244: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
(* usable definition P suppressed *)
fixes y
assumes y_in : "(y \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0]))))))))))))))))))"
fixes z
assumes z_in : "(z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0]))))))))))))))))))"
assumes v'286: "(((fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z)))))"
assumes v'295: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'296: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'297: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'298: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'299: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'300: "((((a_jhash_primea :: c)) = (j)))"
assumes v'301: "((((a_lhash_primea :: c)) = (l)))"
assumes v'302: "((((a_xhash_primea :: c)) = (x)))"
assumes v'303: "((((a_vhash_primea :: c)) = (v)))"
assumes v'304: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca_1. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca_1)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq_1 \<in> ((Perm ((S)))) : ((((fapply ((a_ca_1), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k_1 \<in> ((DOMAIN (seq_1)))  \<mapsto> (fapply ((v), (fapply ((seq_1), (k_1)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca_1), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca_1), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
shows "(((((fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))) = (p))) \<Rightarrow> (((((fapply ((pc), (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))))) \<noteq> (''E2''))) \<and> (((fapply ((pc), (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))))) \<noteq> (''E2'')))))))"(is "PROP ?ob'1890")
proof -
ML_command {* writeln "*** TLAPS ENTER 1890"; *}
show "PROP ?ob'1890"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1890"; *} qed
lemma ob'1861:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) \<rightarrow> (A)]), %f. (\<forall> w \<in> (A) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))) : (((fapply ((f), (q))) = (w))))))))"
assumes v'235: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'236: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'244: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
(* usable definition P suppressed *)
assumes v'281: "((((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))) = ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))))"
assumes v'282: "((((Cardinality ((setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z)))))))) = ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0]))))))))))))))))"
shows "((([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), ((Cardinality ((setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))))))))))) \<rightarrow> (setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z)))))]), %f. (\<forall> w \<in> (setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))))) : (\<exists> q \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))))))))))) : (((fapply ((f), (q))) = (w)))))))))"(is "PROP ?ob'1861")
proof -
ML_command {* writeln "*** TLAPS ENTER 1861"; *}
show "PROP ?ob'1861"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1861"; *} qed
lemma ob'1933:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "(((((((pc) \<in> ([(ProcSet) \<rightarrow> ({(''L0''), (''E1''), (''E2''), (''E3''), (''D1''), (''D2''), (''D3''), (''D4'')})]))) & (((X) \<in> (((Nat) \\ ({((0))}))))) & (((Q) \<in> ([(((Nat) \\ ({((0))}))) \<rightarrow> (((((Nat) \\ ({((0))}))) \<union> ({(BOT)})))]))) & (((i) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((j) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((l) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((x) \<in> ([(ProcSet) \<rightarrow> (((((Nat) \\ ({((0))}))) \<union> ({(BOT)})))]))) & (((v) \<in> ([(ProcSet) \<rightarrow> (((Nat) \\ ({((0))})))]))) & (((M) \<in> ((SUBSET (subsetOf((CDomain), %a_ca. ((CFTypeOK ((a_ca))))))))))) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'235: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'236: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'244: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
(* usable definition P suppressed *)
fixes y
assumes y_in : "(y \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0]))))))))))))))))))"
fixes z
assumes z_in : "(z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0]))))))))))))))))))"
assumes v'286: "(((fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z)))))"
assumes v'304: "(((fapply ((pc), (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))))) = (''E2'')))"
assumes v'305: "(((fapply ((i), (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (y)))))"
assumes v'308: "(((fapply ((pc), (p))) = (''E1'')))"
assumes v'309: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''E2'')])))"
assumes v'310: "((((a_ihash_primea :: c)) = ([(i) EXCEPT ![(p)] = (X)])))"
assumes v'311: "((((a_Xhash_primea :: c)) = ((arith_add ((X), ((Succ[0])))))))"
assumes v'312: "((((a_Qhash_primea :: c)) = (Q)))"
assumes v'313: "((((a_jhash_primea :: c)) = (j)))"
assumes v'314: "((((a_lhash_primea :: c)) = (l)))"
assumes v'315: "((((a_xhash_primea :: c)) = (x)))"
assumes v'316: "((((a_vhash_primea :: c)) = (v)))"
assumes v'317: "((((a_Mhash_primea :: c)) = (subsetOf((CDomain), %a_ca_1. (((a_h022c5783954683bdcbcacced356fd6a ((a_ca_1)) :: c)) & (\<exists> d \<in> (M) : (\<exists> S \<in> ((SUBSET ((hc4e622ce2e33ef1c6a9f10c01956cd ((d)) :: c)))) : (\<exists> seq_1 \<in> ((Perm ((S)))) : ((((fapply ((a_ca_1), (''sigma''))) = ((Concat ((fapply ((d), (''sigma''))), ([ k_1 \<in> ((DOMAIN (seq_1)))  \<mapsto> (fapply ((v), (fapply ((seq_1), (k_1)))))])))))) & (\<forall> q \<in> (ProcSet) : (cond((((q) \<in> (S))), (((fapply ((fapply ((a_ca_1), (''fres''))), (q))) = (ACK))), (((fapply ((fapply ((a_ca_1), (''fres''))), (q))) = (fapply ((fapply ((d), (''fres''))), (q)))))))))))))))))"
shows "(((((fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (y))) \<noteq> (p))) \<and> (((fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))) \<noteq> (p)))))"(is "PROP ?ob'1933")
proof -
ML_command {* writeln "*** TLAPS ENTER 1933"; *}
show "PROP ?ob'1933"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 1933"; *} qed
lemma ob'2158:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'203: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'209: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'235: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'236: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'244: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
(* usable definition d suppressed *)
(* usable definition P suppressed *)
fixes m
assumes m_in : "(m \<in> ((DOMAIN (seq))))"
assumes v'309: "((less ((m), (k))))"
assumes v'310: "(((fapply ((fapply ((d), (''sigma''))), (m))) = (fapply ((fapply ((a_ca), (''sigma''))), (m)))))"
assumes v'317: "(((fapply ((Q), (fapply ((seq), (m))))) = (BOT)))"
fixes q
assumes q_in : "(q \<in> (ProcSet))"
assumes v'331: "((GoodRes ((setOfAll(((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0]))))))))))), %z. (fapply ((seq), (z))))), (fapply ((a_ca), (''fres''))))))"
assumes v'332: "(((fapply ((a_ca), (''sigma''))) = ([ k_1 \<in> ((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))])))  \<mapsto> (CaseOther(<<(((fapply ((Q), (fapply (([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))]), (k_1))))) \<noteq> (BOT)))>>,<<(fapply ((Q), (fapply (([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))]), (k_1)))))>>,(fapply ((v), (bChoice((ProcSet), %q_1. (((((fapply ((pc), (q_1))) = (''E2''))) \<and> (((fapply ((i), (q_1))) = (fapply (([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))]), (k_1)))))))))))))])))"
assumes v'333: "(((m) \<in> ((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add ((k), ((minus (((Succ[0])))))))))))  \<mapsto> (fapply ((seq), (z)))])))))"
assumes v'334: "((((DOMAIN (seq))) = ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A)))))))))"
shows "(((fapply ((fapply ((a_ca), (''sigma''))), (m))) = (fapply ((v), (bChoice((ProcSet), %r. (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply ((seq), (m)))))))))))))"(is "PROP ?ob'2158")
proof -
ML_command {* writeln "*** TLAPS ENTER 2158"; *}
show "PROP ?ob'2158"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 2158"; *} qed
lemma ob'2455:
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
fixes ACK
fixes BOT
fixes ProcSet
fixes pc pc'
fixes X X'
fixes Q Q'
fixes i i'
fixes j j'
fixes l l'
fixes x x'
fixes v v'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition Seqs suppressed *)
(* usable definition Concat suppressed *)
(* usable definition Head suppressed *)
(* usable definition Tail suppressed *)
(* usable definition Init suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition UnlinearizedEnqs suppressed *)
(* usable definition Filter suppressed *)
(* usable definition L0 suppressed *)
(* usable definition E2 suppressed *)
(* usable definition E3 suppressed *)
(* usable definition D1 suppressed *)
(* usable definition D2 suppressed *)
(* usable definition D3 suppressed *)
(* usable definition D4 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv_E2 suppressed *)
(* usable definition Inv_E3 suppressed *)
(* usable definition Inv_D2 suppressed *)
(* usable definition Inv_D3 suppressed *)
(* usable definition Inv_Q suppressed *)
(* usable definition GoodEnqSet suppressed *)
(* usable definition ValuesMatchInds suppressed *)
(* usable definition GoodRes suppressed *)
(* usable definition JInvSeq suppressed *)
(* usable definition Inv_Main suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv suppressed *)
assumes v'204: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'210: "((((TypeOK) & (a_Invunde_E2a) & (a_Invunde_E3a) & (a_Invunde_D2a) & (a_Invunde_D3a) & (a_Invunde_Qa) & (a_Invunde_Maina)) \<and> (((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))))"
fixes p
assumes p_in : "(p \<in> (ProcSet))"
fixes A
assumes A_in : "(A \<in> ((SUBSET ((isa_peri_peri_a (((Succ[0])), ((arith_add (((a_Xhash_primea :: c)), ((minus (((Succ[0]))))))))))))))"
fixes seq
assumes seq_in : "(seq \<in> ((Perm ((A)))))"
assumes v'236: "((a_h809dcbde4a0ebaffb04edba90d34c1a ((A)) :: c))"
assumes v'237: "((a_h76227835d3f4b8a2f4a94c89f14166a ((seq)) :: c))"
assumes v'245: "(((fapply (((a_ihash_primea :: c)), (p))) \<in> (A)))"
fixes k
assumes k_in : "(k \<in> ((isa_peri_peri_a (((Succ[0])), ((Cardinality ((A))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> (M))"
(* usable definition d suppressed *)
(* usable definition P suppressed *)
fixes q
assumes q_in : "(q \<in> (ProcSet))"
assumes v'296: "(((q) \<notin> (setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z)))))))"
assumes v'307: "(((fapply ((i), (q))) \<in> (setOfAll((setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))))), %r. (fapply (((a_ihash_primea :: c)), (r)))))))"
assumes v'308: "(((fapply ((pc), (q))) = (''E2'')))"
fixes r
assumes r_in : "(r \<in> (setOfAll(((DOMAIN ([ z \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_1), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z)))))))))))]))), %z. (fapply (([ z_1 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (bChoice((ProcSet), %r. (((((((r) = (p))) \<and> (((X) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1))))))) \<or> (((((fapply ((pc), (r))) = (''E2''))) \<and> (((fapply ((i), (r))) = (fapply (([ z_2 \<in> ((isa_peri_peri_a (((Succ[0])), ((arith_add (((Cardinality ((A)))), ((minus (((arith_add ((k), ((minus (((Succ[0])))))))))))))))))  \<mapsto> (fapply ((seq), ((arith_add ((z_2), ((arith_add ((k), ((minus (((Succ[0])))))))))))))]), (z_1)))))))))))]), (z))))))"
assumes v'322: "(((r) = (p)))"
assumes v'325: "((less ((fapply ((i), (q))), (X))))"
assumes v'326: "(((fapply (((a_ihash_primea :: c)), (p))) = (X)))"
assumes v'327: "(((fapply ((i), (q))) = (fapply (((a_ihash_primea :: c)), (r)))))"
shows "(((r) = (q)))"(is "PROP ?ob'2455")
proof -
ML_command {* writeln "*** TLAPS ENTER 2455"; *}
show "PROP ?ob'2455"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 2455"; *} qed
end
