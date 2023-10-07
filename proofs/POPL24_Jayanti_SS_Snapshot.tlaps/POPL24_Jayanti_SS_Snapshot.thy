(* automatically generated -- do not edit manually *)
theory POPL24_Jayanti_SS_Snapshot imports Constant Zenon begin
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

lemma ob'494:
fixes ACK
fixes BOT
fixes K
fixes WriteSet
fixes S
fixes pc pc'
fixes X X'
fixes A A'
fixes B B'
fixes a a'
fixes i i'
fixes v v'
fixes j j'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition IndexSet suppressed *)
(* usable definition Map suppressed *)
(* usable definition Merge suppressed *)
(* usable definition Init suppressed *)
(* usable definition L0 suppressed *)
(* usable definition W1 suppressed *)
(* usable definition W2 suppressed *)
(* usable definition W3 suppressed *)
(* usable definition W4 suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition KthReturnSet suppressed *)
(* usable definition ScanReturnSet suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv_W0 suppressed *)
(* usable definition Inv_W1 suppressed *)
(* usable definition Inv_W2 suppressed *)
(* usable definition Inv_W3 suppressed *)
(* usable definition Inv_S1 suppressed *)
(* usable definition Inv_S2 suppressed *)
(* usable definition Inv_S3 suppressed *)
(* usable definition Inv_M1 suppressed *)
(* usable definition Inv_M2 suppressed *)
assumes v'54: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'55: "(((S) \<notin> (WriteSet)))"
assumes v'56: "(((K) \<in> (((Nat) \\ ({((0))})))))"
assumes v'62: "((TypeOK) & (a_Invunde_W0a) & (a_Invunde_W1a) & (a_Invunde_W2a) & (a_Invunde_W3a) & (\<forall> k \<in> (IndexSet) : (\<forall> a_ca \<in> (M) : (((\<forall> p \<in> (WriteSet) : (((((fapply ((pc), (p))) \<in> ({(''L0''), (''W1'')}))) \<or> (((fapply ((i), (p))) \<noteq> (k)))))) \<Rightarrow> (((fapply ((fapply ((a_ca), (''sigma''))), (k))) = (fapply ((A), (k))))))))) & (a_Invunde_S1a) & (a_Invunde_S2a) & (a_Invunde_S3a) & (a_Invunde_M1a) & (a_Invunde_M2a) & (Linearizable))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
assumes v'85: "(((fapply ((pc), (S))) = (''S4'')))"
assumes v'86: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(S)] = (''S5'')])))"
assumes v'87: "((((a_jhash_primea :: c)) = ((0))))"
assumes v'88: "((((a_Xhash_primea :: c)) = (FALSE)))"
assumes v'89: "((((a_Ahash_primea :: c)) = (A)))"
assumes v'90: "((((a_Bhash_primea :: c)) = (B)))"
assumes v'91: "((((a_ahash_primea :: c)) = (a)))"
assumes v'92: "((((a_ihash_primea :: c)) = (i)))"
assumes v'93: "((((a_vhash_primea :: c)) = (v)))"
assumes v'94: "((((a_jhash_primea :: c)) = (j)))"
assumes v'95: "((((a_Mhash_primea :: c)) = (setOfAll((M), %a_ca. (((''sigma'' :> (A)) @@ (''fres'' :> ((Merge (([ w \<in> (WriteSet)  \<mapsto> (cond((((fapply ((pc), (w))) \<in> ({(''W2''), (''W3''), (''W4'')}))), (ACK), (BOT)))]), ((Map ((S), (fapply ((a_ca), (''sigma''))))))))))))))))"
shows "(\<forall> k \<in> (IndexSet) : (\<forall> a_ca \<in> ((a_Mhash_primea :: c)) : (((\<forall> p \<in> (WriteSet) : (((((fapply (((a_pchash_primea :: c)), (p))) \<in> ({(''L0''), (''W1'')}))) \<or> (((fapply (((a_ihash_primea :: c)), (p))) \<noteq> (k)))))) \<Rightarrow> (((fapply ((fapply ((a_ca), (''sigma''))), (k))) = (fapply (((a_Ahash_primea :: c)), (k)))))))))"(is "PROP ?ob'494")
proof -
ML_command {* writeln "*** TLAPS ENTER 494"; *}
show "PROP ?ob'494"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 494"; *} qed
lemma ob'248:
fixes ACK
fixes BOT
fixes K
fixes WriteSet
fixes S
fixes pc pc'
fixes X X'
fixes A A'
fixes B B'
fixes a a'
fixes i i'
fixes v v'
fixes j j'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition IndexSet suppressed *)
(* usable definition Map suppressed *)
(* usable definition Merge suppressed *)
(* usable definition Init suppressed *)
(* usable definition L0 suppressed *)
(* usable definition W1 suppressed *)
(* usable definition W2 suppressed *)
(* usable definition W3 suppressed *)
(* usable definition W4 suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition KthReturnSet suppressed *)
(* usable definition ScanReturnSet suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv_W0 suppressed *)
(* usable definition Inv_W2 suppressed *)
(* usable definition Inv_W3 suppressed *)
(* usable definition Inv_W4 suppressed *)
(* usable definition Inv_S1 suppressed *)
(* usable definition Inv_S2 suppressed *)
(* usable definition Inv_S3 suppressed *)
(* usable definition Inv_M1 suppressed *)
(* usable definition Inv_M2 suppressed *)
assumes v'54: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'55: "(((S) \<notin> (WriteSet)))"
assumes v'56: "(((K) \<in> (((Nat) \\ ({((0))})))))"
assumes v'62: "((TypeOK) & (a_Invunde_W0a) & (\<forall> p \<in> (WriteSet) : (\<forall> a_ca \<in> (M) : (((((((fapply ((pc), (p))) \<in> ({(''W2''), (''W3''), (''W4'')}))) \<and> (((fapply ((fapply ((a_ca), (''sigma''))), (fapply ((i), (p))))) \<noteq> (fapply ((A), (fapply ((i), (p))))))))) \<Rightarrow> (((fapply ((fapply ((a_ca), (''fres''))), (p))) = (BOT))))))) & (a_Invunde_W2a) & (a_Invunde_W3a) & (a_Invunde_W4a) & (a_Invunde_S1a) & (a_Invunde_S2a) & (a_Invunde_S3a) & (a_Invunde_M1a) & (a_Invunde_M2a) & (Linearizable))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
assumes v'82: "(((fapply ((pc), (S))) = (''S4'')))"
assumes v'83: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(S)] = (''S5'')])))"
assumes v'84: "((((a_jhash_primea :: c)) = ((0))))"
assumes v'85: "((((a_Xhash_primea :: c)) = (FALSE)))"
assumes v'86: "((((a_Ahash_primea :: c)) = (A)))"
assumes v'87: "((((a_Bhash_primea :: c)) = (B)))"
assumes v'88: "((((a_ahash_primea :: c)) = (a)))"
assumes v'89: "((((a_ihash_primea :: c)) = (i)))"
assumes v'90: "((((a_vhash_primea :: c)) = (v)))"
assumes v'91: "((((a_jhash_primea :: c)) = (j)))"
assumes v'92: "((((a_Mhash_primea :: c)) = (setOfAll((M), %a_ca. (((''sigma'' :> (A)) @@ (''fres'' :> ((Merge (([ w \<in> (WriteSet)  \<mapsto> (cond((((fapply ((pc), (w))) \<in> ({(''W2''), (''W3''), (''W4'')}))), (ACK), (BOT)))]), ((Map ((S), (fapply ((a_ca), (''sigma''))))))))))))))))"
shows "(\<forall> p \<in> (WriteSet) : (\<forall> a_ca \<in> ((a_Mhash_primea :: c)) : (((((((fapply (((a_pchash_primea :: c)), (p))) \<in> ({(''W2''), (''W3''), (''W4'')}))) \<and> (((fapply ((fapply ((a_ca), (''sigma''))), (fapply (((a_ihash_primea :: c)), (p))))) \<noteq> (fapply (((a_Ahash_primea :: c)), (fapply (((a_ihash_primea :: c)), (p))))))))) \<Rightarrow> (((fapply ((fapply ((a_ca), (''fres''))), (p))) = (BOT)))))))"(is "PROP ?ob'248")
proof -
ML_command {* writeln "*** TLAPS ENTER 248"; *}
show "PROP ?ob'248"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 248"; *} qed
lemma ob'208:
fixes ACK
fixes BOT
fixes K
fixes WriteSet
fixes S
fixes pc pc'
fixes X X'
fixes A A'
fixes B B'
fixes a a'
fixes i i'
fixes v v'
fixes j j'
fixes M M'
(* usable definition vars suppressed *)
(* usable definition IndexSet suppressed *)
(* usable definition Map suppressed *)
(* usable definition Merge suppressed *)
(* usable definition Init suppressed *)
(* usable definition L0 suppressed *)
(* usable definition W1 suppressed *)
(* usable definition W2 suppressed *)
(* usable definition W3 suppressed *)
(* usable definition W4 suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition CFTypeOK suppressed *)
(* usable definition CDomain suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition KthReturnSet suppressed *)
(* usable definition ScanReturnSet suppressed *)
(* usable definition Linearizable suppressed *)
(* usable definition Inv_W1 suppressed *)
(* usable definition Inv_W2 suppressed *)
(* usable definition Inv_W3 suppressed *)
(* usable definition Inv_W4 suppressed *)
(* usable definition Inv_S1 suppressed *)
(* usable definition Inv_S2 suppressed *)
(* usable definition Inv_S3 suppressed *)
(* usable definition Inv_M1 suppressed *)
(* usable definition Inv_M2 suppressed *)
assumes v'54: "((((ACK) \<noteq> (BOT))) & (((BOT) \<notin> (Nat))))"
assumes v'55: "(((S) \<notin> (WriteSet)))"
assumes v'56: "(((K) \<in> (((Nat) \\ ({((0))})))))"
assumes v'62: "((TypeOK) & (\<forall> p \<in> (WriteSet) : (\<forall> a_ca \<in> (M) : (((((fapply ((pc), (p))) = (''W1''))) \<Rightarrow> (((fapply ((fapply ((a_ca), (''sigma''))), (fapply ((i), (p))))) = (fapply ((A), (fapply ((i), (p))))))))))) & (a_Invunde_W1a) & (a_Invunde_W2a) & (a_Invunde_W3a) & (a_Invunde_W4a) & (a_Invunde_S1a) & (a_Invunde_S2a) & (a_Invunde_S3a) & (a_Invunde_M1a) & (a_Invunde_M2a) & (Linearizable))"
assumes v'63: "(((Next) \<or> ((((a_h4fd5f73954dc53af536c1c75068837a :: c)) = (vars)))))"
assumes v'81: "(((fapply ((pc), (S))) = (''S4'')))"
assumes v'82: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(S)] = (''S5'')])))"
assumes v'83: "((((a_jhash_primea :: c)) = ((0))))"
assumes v'84: "((((a_Xhash_primea :: c)) = (FALSE)))"
assumes v'85: "((((a_Ahash_primea :: c)) = (A)))"
assumes v'86: "((((a_Bhash_primea :: c)) = (B)))"
assumes v'87: "((((a_ahash_primea :: c)) = (a)))"
assumes v'88: "((((a_ihash_primea :: c)) = (i)))"
assumes v'89: "((((a_vhash_primea :: c)) = (v)))"
assumes v'90: "((((a_jhash_primea :: c)) = (j)))"
assumes v'91: "((((a_Mhash_primea :: c)) = (setOfAll((M), %a_ca. (((''sigma'' :> (A)) @@ (''fres'' :> ((Merge (([ w \<in> (WriteSet)  \<mapsto> (cond((((fapply ((pc), (w))) \<in> ({(''W2''), (''W3''), (''W4'')}))), (ACK), (BOT)))]), ((Map ((S), (fapply ((a_ca), (''sigma''))))))))))))))))"
shows "(\<forall> p \<in> (WriteSet) : (\<forall> a_ca \<in> ((a_Mhash_primea :: c)) : (((((fapply (((a_pchash_primea :: c)), (p))) = (''W1''))) \<Rightarrow> (((fapply ((fapply ((a_ca), (''sigma''))), (fapply (((a_ihash_primea :: c)), (p))))) = (fapply (((a_Ahash_primea :: c)), (fapply (((a_ihash_primea :: c)), (p)))))))))))"(is "PROP ?ob'208")
proof -
ML_command {* writeln "*** TLAPS ENTER 208"; *}
show "PROP ?ob'208"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 208"; *} qed
end
