theory CoronaAppThree
  imports InfrastructureThree
begin
locale scenarioCoronaThree = scenarioCoronaTwo +

fixes corona_actorsR :: "identity set"
defines corona_actorsR_def: "corona_actorsR \<equiv> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}"

fixes corona_locationsR :: "location set"
defines corona_locationsR_def: "corona_locationsR \<equiv> {Location 0, Location 1}"
fixes pubR :: "location"
defines pubR_def: "pubR \<equiv> Location 0"
fixes shopR :: "location"
defines shopR_def: "shopR \<equiv> Location 1"

fixes identifiableR' :: "[efid, (identity * efid)set] \<Rightarrow> bool"
defines identifiableR'_def: "identifiableR' eid A \<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> A \<and> Eid = eid}"

fixes global_policyR'' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyR''_def: "global_policyR'' I eid \<equiv>  
             \<not>(identifiableR' eid 
                ((\<Inter> (kgra(graphI I)(''Eve'')`(nodes(graphI I))))
                 - {(x,y). x = ''Eve''}))"

(* The intersection above might be empty yet there could be individual l: nodes (graphI I)
   for which identifiability is given*)
fixes global_policyR' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyR'_def: "global_policyR' I eid \<equiv>  
             \<forall> l \<in> nodes(graphI I). \<not>(identifiableR' eid 
                (kgra(graphI I)(''Eve'') l - {(x,y). x = ''Eve''}))"

(* The strongest one and the one we need is the following policy. *)
fixes global_policyR :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyR_def: "global_policyR I eid \<equiv>  
             \<forall> L. 0 < card L \<longrightarrow> L \<subseteq> nodes(graphI I) \<longrightarrow> (\<not>(identifiableR' eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L)
                          - {(x,y). x = ''Eve''}))))"

fixes ex_credsR :: "identity \<Rightarrow> efidlist"
defines ex_credsR_def: 
          "ex_credsR \<equiv>  (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 0 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"
(*
fixes ex_credsR' :: "identity \<Rightarrow> efidlist"
defines ex_credsR'_def: 
          "ex_credsR' \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 1 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (13^(n+1)))))))))"

fixes ex_credsR'' :: "identity \<Rightarrow> efidlist"
defines ex_credsR''_def: 
          "ex_credsR'' \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 1 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 1 (\<lambda> n. Efid (11^(n+1)))) else 
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (13^(n+1)))))))))"
*)
fixes ex_locsR :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locsR \<equiv> (\<lambda> x. ('''',{}))"

fixes ex_loc_assR :: "location \<Rightarrow> identity set"
defines ex_loc_assR_def: "ex_loc_assR \<equiv>
          (\<lambda> x. if x = pubR then {''Alice'', ''Bob'', ''Eve''}  
                 else (if x = shopR then {''Charly'', ''David'', ''Flo''} 
                       else {}))"
(*
fixes ex_loc_assR' :: "location \<Rightarrow> identity set"
defines ex_loc_assR'_def: "ex_loc_assR' \<equiv>
          (\<lambda> x. if x = pubR then {''Alice'', ''Eve''}  
                 else (if x = shopR then { ''Bob'', ''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_assR'' :: "location \<Rightarrow> identity set"
defines ex_loc_assR''_def: "ex_loc_assR'' \<equiv>
          (\<lambda> x. if x = pubR then {''Alice''}  
                 else (if x = shopR then {''Eve'', ''Bob'', ''Charly'', ''David''} 
                       else {}))"
*)
fixes ex_efidsR :: "location \<Rightarrow> efid set"
defines ex_efidsR_def: "ex_efidsR \<equiv> 
          (\<lambda> x. if x = pubR then {Efid 2, Efid 3, Efid 11}
                else (if x = shopR then {Efid 5, Efid 7, Efid 13}
                      else {}))"
(*
fixes ex_efidsR' :: "location \<Rightarrow> efid set"
defines ex_efidsR'_def: "ex_efidsR' \<equiv> 
          (\<lambda> x. if x = pubR then {Efid 2, Efid 11}
                else (if x = shopR then {Efid 9, Efid 5, Efid 7}
                      else {}))"

fixes ex_efidsR'' :: "location \<Rightarrow> efid set"
defines ex_efidsR''_def: "ex_efidsR'' \<equiv> 
          (\<lambda> x. if x = pubR then {Efid 2}
                else (if x = shopR then {Efid 121, Efid 3, Efid 5, Efid 7}
                      else {}))"
*)
fixes ex_knosR :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosR_def: "ex_knosR \<equiv> (\<lambda> x :: identity. 
                  (if x = ''Eve'' then (\<lambda> l :: location. {} :: (identity * efid) set) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"
(*
fixes ex_knosR' :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosR'_def: "ex_knosR' \<equiv> (\<lambda> x :: identity. 
                  (if x = ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubR then 
                                  ({(''Alice'', Efid 2),(''Alice'', Efid 3),(''Alice'', Efid 11),
                                    (''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 11)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosR'' :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosR''_def: "ex_knosR'' \<equiv> (\<lambda> x :: identity.                       
                  (if x = ''Eve'' then 
                      (\<lambda> l :: location.
                           (if l = pubR then 
                                  ({(''Alice'', Efid 2),(''Alice'', Efid 3),(''Alice'', Efid 11),
                                    (''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 11)})
                            else (if l = shopR then 
                                     ({(''Eve'', Efid 121),(''Eve'', Efid 9),(''Eve'', Efid 5),(''Eve'', Efid 7),
                                       (''Bob'', Efid 121),(''Bob'', Efid 9),(''Bob'', Efid 5),(''Bob'', Efid 7), 
                                       (''Charly'', Efid 121),(''Charly'', Efid 9),(''Charly'', Efid 5),(''Charly'', Efid 7),
                                       (''David'', Efid 121),(''David'', Efid 9),(''David'', Efid 5),(''David'', Efid 7)})
                                   else {})))
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"
*)
(* The nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax)  
fixes ex_loc_ass_alt :: "location \<Rightarrow> identity set"
defines ex_loc_ass_alt_def: "ex_loc_ass_alt \<equiv>
          (\<lambda> x.  (case x of 
             Location (Suc 0) \<Rightarrow> {''Alice'', ''Bob'', ''Eve''}  
           | Location (Suc (Suc 0)) \<Rightarrow> {''Charly'', ''David''} 
           |  _ \<Rightarrow> {}))"
*)
(* Alternative attack that persisted even in Level Two: 
   Bob gets isolated by Alice leaving pub so he's alone with Eve.
   Here in level 3 it should not persist any more because we have the number of actors
   restriction in the locations. *)
fixes ex_credsRi :: "identity \<Rightarrow> efidlist"
defines ex_credsRi_def: 
          "ex_credsRi \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 1 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 0 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else 
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"

fixes ex_loc_assRi :: "location \<Rightarrow> identity set"
defines ex_loc_assRi_def: "ex_loc_assRi \<equiv>
          (\<lambda> x. if x = pubR then {''Bob'', ''Eve''}  
                 else (if x = shopR then {''Alice'', ''Charly'', ''David'',''Flo''} 
                       else {}))"

fixes ex_efidsRi :: "location \<Rightarrow> efid set"
defines ex_efidsRi_def: "ex_efidsRi \<equiv> 
          (\<lambda> x. if x = pubR then {Efid 3, Efid 11}
                else (if x = shopR then {Efid 4, Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_knosRi :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosRi_def: "ex_knosRi \<equiv>(\<lambda> x :: identity. 
                  (if x = ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubR then 
                                  ({(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 3),(''Eve'', Efid 11)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"


(* initial *)
fixes ex_graphR :: "igraph"
defines ex_graphR_def: "ex_graphR \<equiv> Lgraph {(pubR, shopR)} ex_loc_assR ex_credsR ex_locsR ex_efidsR ex_knosR"

(* Eve gets the ex_knos 
fixes ex_graphR' :: "igraph"
defines ex_graphR'_def: "ex_graphR' \<equiv> Lgraph {(pubR, shopR)} ex_loc_assR ex_credsR ex_locsR ex_efidsR ex_knosR'"
*)
(* Bob goes to shop 
fixes ex_graphR'' :: "igraph"
defines ex_graphR''_def: "ex_graphR'' \<equiv> Lgraph {(pubR, shopR)} ex_loc_assR' ex_credsR ex_locsR ex_efidsR' ex_knosR'"
*)
(* Eve goes to shop 
fixes ex_graphR''' :: "igraph"
defines ex_graphR'''_def: "ex_graphR''' \<equiv> Lgraph {(pubR, shopR)} ex_loc_assR'' ex_credsR ex_locsR ex_efidsR'' ex_knosR'"
*)
(* Eve gets ex_knos at shop 
fixes ex_graphR'''' :: "igraph"
defines ex_graphR''''_def: "ex_graphR'''' \<equiv> Lgraph {(pubR, shopR)} ex_loc_assR'' ex_credsR ex_locsR ex_efidsR'' ex_knosR''"
*)
(* Same as above: the nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax) 
fixes local_policies_alt :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_alt_def: "local_policies_alt G \<equiv> 
    (\<lambda> x. case x of 
         Location (Suc 0) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location 0 \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
       | Location (Suc (Suc (Suc 0))) \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
       | Location (Suc (Suc 0)) \<Rightarrow>
                {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
       | _ \<Rightarrow>  {})"
*)
(* Second attack: Alice goes and then Bob is alone with Eve, so Eve can get and make the identification *)
(* Alice goes to shop*)
fixes ex_graphRi :: "igraph"
defines ex_graphRi_def: "ex_graphRi \<equiv> Lgraph {(pubR, shopR)} ex_loc_assRi ex_credsRi ex_locsT ex_efidsRi ex_knosR"

(* Eve gets the ex_knos *)
fixes ex_graphRii :: "igraph"
defines ex_graphRii_def: "ex_graphRii \<equiv> Lgraph {(pubR, shopR)} ex_loc_assRi ex_credsRi ex_locsR ex_efidsRi ex_knosRi"

fixes local_policiesR :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesR_def: "local_policiesR G \<equiv> 
    (\<lambda> x. if x = pubR then  {(\<lambda> y. True, {get,move})}
          else (if x = shopR then {(\<lambda> y. True, {get,move})} 
                else {}))"

(* problems with case in locales?
defines local_policies_def: "local_policies G x \<equiv> 
     (case x of 
       home \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | sphone \<Rightarrow> {((\<lambda> y. has G (y, ''PIN'')), {put,get,move,eval})} 
     | cloud \<Rightarrow> {(\<lambda> y. True, {put,get,move,eval})}
     | hospital \<Rightarrow> {((\<lambda> y. (\<exists> n. (n  @\<^bsub>G\<^esub> hospital) \<and> Actor n = y \<and> 
                           has G (y, ''skey''))), {put,get,move,eval})} 
     | _ \<Rightarrow>  {})"
*)

fixes rmapR :: "InfrastructureThree.infrastructure \<Rightarrow> InfrastructureTwo.infrastructure"
defines rmapR_def:
"rmapR I \<equiv> InfrastructureThree.ref_map I local_policiesT"

fixes corona_scenarioR :: "infrastructure"
defines corona_scenarioR_def:
"corona_scenarioR \<equiv> Infrastructure ex_graphR local_policiesR"
fixes IcoronaR :: "infrastructure set"
defines IcoronaR_def:
  "IcoronaR \<equiv> {corona_scenarioR}"

(* other states of scenario *)
(* First step: Bob goes to shop *)
(*
fixes corona_scenarioR' :: "infrastructure"
defines corona_scenarioR'_def: "corona_scenarioR' \<equiv> Infrastructure ex_graphR' local_policiesR"
fixes CoronaR' :: "infrastructure set"
defines CoronaR'_def: "CoronaR' \<equiv> {corona_scenarioR'}"
fixes corona_scenarioR'' :: "infrastructure"
defines corona_scenarioR''_def: "corona_scenarioR'' \<equiv> Infrastructure ex_graphR'' local_policiesR"
fixes CoronaR'' :: "infrastructure set"
defines Corona''_def: "CoronaR'' \<equiv> {corona_scenarioR''}"
fixes corona_scenarioR''' :: "infrastructure"
defines corona_scenarioR'''_def: "corona_scenarioR''' \<equiv> Infrastructure ex_graphR''' local_policiesR"
fixes CoronaR''' :: "infrastructure set"
defines CoronaR'''_def: "CoronaR''' \<equiv> {corona_scenarioR'''}"
fixes corona_scenarioR'''' :: "infrastructure"
defines corona_scenarioR''''_def: "corona_scenarioR'''' \<equiv> Infrastructure ex_graphR'''' local_policiesR"
fixes CoronaR'''' :: "infrastructure set"
defines CoronaR''''_def: "CoronaR'''' \<equiv> {corona_scenarioR''''}"
*)
(* Second attack where Alice leaves *)
fixes corona_scenarioRi :: "infrastructure"
defines corona_scenarioRi_def: "corona_scenarioRi \<equiv> Infrastructure ex_graphRi local_policiesR"
fixes CoronaRi :: "infrastructure set"
defines CoronaRi_def: "CoronaRi \<equiv> {corona_scenarioRi}" 
fixes corona_scenarioRii :: "infrastructure" 
defines corona_scenarioRii_def: "corona_scenarioRii \<equiv> Infrastructure ex_graphRii local_policiesR" 
fixes CoronaRii :: "infrastructure set"
defines CoronaRii_def: "CoronaRii \<equiv> {corona_scenarioRii}"

fixes corona_statesR
defines corona_statesR_def: "corona_statesR \<equiv> { I. corona_scenarioR \<rightarrow>\<^sub>i* I }"
fixes corona_KripkeR
defines "corona_KripkeR \<equiv> Kripke corona_statesR IcoronaR"
fixes scoronaR 
defines "scoronaR \<equiv> {x. \<exists> n. \<not> global_policyR'' x (Efid n)}"  
fixes scoronaR' 
defines "scoronaR' \<equiv> {x. \<exists> n. \<not> global_policyR x (Efid n)}"  
(* *)
begin
(* actor invariants for example *)
lemma all_actors: "actors_graph(graphI corona_scenarioR) = corona_actorsR"
proof (simp add: corona_scenarioR_def corona_actorsR_def ex_graphR_def actors_graph_def nodes_def
                 ex_loc_assR_def, rule equalityI)
  show "{x. \<exists>y. (y = shopR \<longrightarrow>
             (shopR = pubR \<longrightarrow> x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'') \<and>
             (shopR \<noteq> pubR \<longrightarrow> x = ''Charly'' \<or> x = ''David'' \<or> x = ''Flo'')) \<and>
            (y \<noteq> shopR \<longrightarrow>
             (y = pubR \<longrightarrow> (\<exists>y. y = shopR \<or> y = pubR \<and> pubR = shopR) \<and> (x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'')) \<and>
             y = pubR)}
    \<subseteq> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}"
    by fastforce
next show "{''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}
    \<subseteq> {x. \<exists>y. (y = shopR \<longrightarrow>
                (shopR = pubR \<longrightarrow> x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'') \<and>
                (shopR \<noteq> pubR \<longrightarrow> x = ''Charly'' \<or> x = ''David'' \<or> x = ''Flo'')) \<and>
               (y \<noteq> shopR \<longrightarrow>
                (y = pubR \<longrightarrow> (\<exists>y. y = shopR \<or> y = pubR \<and> pubR = shopR) \<and> (x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'')) \<and>
                y = pubR)}"
    using pubR_def shopR_def by auto
qed

lemma all_corona_actors: "(corona_scenarioR, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI y) = corona_actorsR"
  using all_actors same_actors by auto

lemma numbers_acors_inv_corona_scenarioR: "l \<in> nodes (graphI corona_scenarioR) \<Longrightarrow>
card (agra (graphI corona_scenarioR) l) \<ge> 2"
  by (simp add: corona_scenarioR_def corona_actorsR_def ex_graphR_def actors_graph_def nodes_def
                 ex_loc_assR_def shopR_def pubR_def, force)

lemma numbers_actors_inv_corona_scenarioR: "l \<in> nodes (graphI corona_scenarioR) \<Longrightarrow>
card (agra (graphI corona_scenarioR) l) \<ge> 3"
  by (simp add: corona_scenarioR_def corona_actorsR_def ex_graphR_def actors_graph_def nodes_def
                 ex_loc_assR_def shopR_def pubR_def, force)

lemma actors_unique_init_lem: "\<forall>a l l'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) \<longrightarrow>
       a \<in> InfrastructureThree.agra (InfrastructureThree.graphI corona_scenarioR) l \<longrightarrow>
       a \<in> InfrastructureThree.agra (InfrastructureThree.graphI corona_scenarioR) l' \<longrightarrow> l = l'"
  by (simp add: corona_scenarioR_def ex_graphR_def ex_loc_assR_def nodes_def ex_credsR_def ex_efidsR_def
             shopR_def pubR_def ex_knosR_def ex_locsR_def actors_graph_def)


(* nodes invariants *)
lemma same_nodes: "(corona_scenarioR, s) \<in> {(x::InfrastructureThree.infrastructure, y::InfrastructureThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> InfrastructureThree.nodes (graphI corona_scenarioR) = InfrastructureThree.nodes (graphI s)"
  using InfrastructureThree.same_nodes by blast


(* efids invariants *)

lemma isthere_lem00: " a \<in>  agra (graphI corona_scenarioR) l \<Longrightarrow> l \<in> nodes (graphI corona_scenarioR) \<Longrightarrow>
            efids_cur (cgra (graphI corona_scenarioR) a) \<in> egra (graphI corona_scenarioR) l"
  apply (simp add: corona_scenarioR_def ex_graphR_def ex_loc_assR_def nodes_def ex_credsR_def ex_efidsR_def
             shopR_def pubR_def)
  by (smt (z3) One_nat_def Zero_not_Suc char.inject insertE list.inject location.inject shopR_def singleton_iff)


lemma efids_root_lem: "a \<in> actors_graph (InfrastructureThree.graphI corona_scenarioR) \<Longrightarrow> 
                      a' \<in> actors_graph (InfrastructureThree.graphI corona_scenarioR) \<Longrightarrow>
                 a \<noteq> a' \<Longrightarrow>
                  efids_root (cgra (InfrastructureThree.graphI corona_scenarioR) a) \<noteq> 
                  efids_root (cgra (InfrastructureThree.graphI corona_scenarioR) a')"
    apply (simp add: rmapR_def ref_map_def move_graph_a_def  corona_scenarioR_def)
  apply (simp add: repl_efr_def ex_graphR_def ex_credsR_def)
  by (smt CollectD InfrastructureThree.actors_graph_def InfrastructureThree.agra.simps InfrastructureThree.gra.simps InfrastructureThree.nodes_def ex_loc_assR_def insertE prod.inject singletonD)

(*
lemma efids_root_minus: "(corona_scenarioR, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
      \<Longrightarrow> a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l 
      \<Longrightarrow> l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I)  \<Longrightarrow>
(\<lambda>x. efids_root (InfrastructureThree.cgra (InfrastructureThree.graphI I) x)) `
       (InfrastructureThree.agra (InfrastructureThree.graphI I) l - {a}) =
       (\<lambda>a. efids_root (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) `
       InfrastructureThree.agra (InfrastructureThree.graphI I) l -
       {efids_root (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)}"
  apply auto
  apply (frule InfrastructureThree.eroots_inj_on_inv)
  sorry
  using efids_root_lem inj_on_def apply blast
  by (metis (mono_tags, lifting) InfrastructureThree.actors_graph_def inj_on_def mem_Collect_eq)
*)
(* efids_list initial invariants*)

lemma efid_in_range_corona_scenarioR: "(\<forall> l \<in> nodes (graphI corona_scenarioR).
         (\<forall> e \<in> (egra (InfrastructureThree.graphI corona_scenarioR) l).
         (\<exists> a \<in> actors_graph (graphI corona_scenarioR). 
             e \<in> range (efids_list (InfrastructureThree.cgra (graphI corona_scenarioR) a)))))"
  apply (simp add: corona_scenarioR_def ex_graphR_def nodes_def)
  apply (rule allI)
   apply (rule impI)+
   apply (rule ballI)
  apply (simp add: ex_efidsR_def actors_graph_def ex_loc_assR_def)
  apply (erule exE)
  apply (erule disjE)
   apply (simp add: pubR_def shopR_def ex_credsR_def nodes_def)
   apply (erule disjE)
    apply (rule_tac x = "''Alice''" in exI)
  apply simp
    apply blast
   apply (erule disjE)
  apply (rule_tac x = "''Bob''" in exI)
  apply simp
    apply blast
   apply (rule_tac x = "''Eve''" in exI)
  apply simp
    apply blast
   apply (simp add: pubR_def shopR_def ex_credsR_def nodes_def)
   apply (erule disjE)
   apply (rule_tac x = "''Charly''" in exI)
  apply simp
   apply (erule disjE)
   apply (rule_tac x = "''David''" in exI)
  apply simp
  apply (rule_tac x = "''Flo''" in exI)
  by simp

lemma efid_kgra_in_range_corona_scenarioR: "(\<forall> l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR). 
         (\<forall> h \<in> InfrastructureThree.actors_graph(InfrastructureThree.graphI corona_scenarioR).
         (\<forall> e \<in> (snd`((InfrastructureThree.kgra (InfrastructureThree.graphI corona_scenarioR) h l))).
         (\<exists> a \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI corona_scenarioR). 
           e \<in> range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI corona_scenarioR) a))))))"
  by (simp add: corona_scenarioR_def ex_graphR_def nodes_def
                 ex_credsR_def ex_locsR_def ex_efidsR_def ex_knosR_def pubR_def shopR_def)

lemma efid_eq_efid_cur_corona_scenarioR: "lb \<in> InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) \<Longrightarrow>
       e \<in> InfrastructureThree.egra (InfrastructureThree.graphI corona_scenarioR) lb \<Longrightarrow>
       \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI corona_scenarioR) lb.
          e = efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI corona_scenarioR) a)"
  apply (simp add: corona_scenarioR_def ex_graphR_def nodes_def ex_loc_assR_def 
                 ex_credsR_def ex_locsR_def ex_efidsR_def ex_knosR_def pubR_def shopR_def)
  using shopR_def by fastforce


lemma not_ex_elem_empty_int: "\<not>(\<exists> x. (x \<in> A \<and> x \<in> B)) \<Longrightarrow> A \<inter> B = {}"
  by (rule no_elem_inter_disjoint)

lemma range_disjoint_corona_scenarioR[rule_format]: "\<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI corona_scenarioR).
       \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI corona_scenarioR).
          a \<noteq> a' \<longrightarrow>
          range
           (InfrastructureThree.efids_list
             (InfrastructureThree.cgra (InfrastructureThree.graphI corona_scenarioR) a)) \<inter>
          range
           (InfrastructureThree.efids_list
             (InfrastructureThree.cgra (InfrastructureThree.graphI corona_scenarioR) a')) =
          {}"
proof (unfold corona_scenarioR_def ex_graphR_def ex_credsR_def, simp)
  show " \<forall>a\<in>InfrastructureThree.actors_graph
         (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
           (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                     else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                          else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                               else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                    else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                         else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
           ex_locsR ex_efidsR ex_knosR).
       (a = ''Flo'' \<longrightarrow>
        (\<forall>a'\<in>InfrastructureThree.actors_graph
               (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                 (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                      else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                           else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                     else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                          else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                               else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                 ex_locsR ex_efidsR ex_knosR).
            (a' = ''Eve'' \<longrightarrow> range (\<lambda>x. Efid (13 * 13 ^ x)) \<inter> range (\<lambda>x. Efid (11 * 11 ^ x)) = {}) \<and>
            (a' \<noteq> ''Eve'' \<longrightarrow>
             (a' = ''David'' \<longrightarrow> range (\<lambda>x. Efid (13 * 13 ^ x)) \<inter> range (\<lambda>x. Efid (7 * 7 ^ x)) = {}) \<and>
             (a' \<noteq> ''David'' \<longrightarrow>
              (a' = ''Charly'' \<longrightarrow> range (\<lambda>x. Efid (13 * 13 ^ x)) \<inter> range (\<lambda>x. Efid (5 * 5 ^ x)) = {}) \<and>
              (a' \<noteq> ''Charly'' \<longrightarrow>
               (a' = ''Bob'' \<longrightarrow> range (\<lambda>x. Efid (13 * 13 ^ x)) \<inter> range (\<lambda>x. Efid (3 * 3 ^ x)) = {}) \<and>
               (a' \<noteq> ''Bob'' \<longrightarrow>
                (a' = ''Alice'' \<longrightarrow> range (\<lambda>x. Efid (13 * 13 ^ x)) \<inter> range (\<lambda>x. Efid (2 * 2 ^ x)) = {}) \<and>
                (a' \<noteq> ''Alice'' \<longrightarrow>
                 ''Flo'' \<noteq> a' \<longrightarrow> range (\<lambda>x. Efid (13 * 13 ^ x)) \<inter> range (\<lambda>x. Efid (17 * 17 ^ x)) = {}))))))) \<and>
       (a \<noteq> ''Flo'' \<longrightarrow>
        (a = ''Eve'' \<longrightarrow>
         (\<forall>a'\<in>InfrastructureThree.actors_graph
                (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                  (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                       else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                            else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                 else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                      else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                           else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                  ex_locsR ex_efidsR ex_knosR).
             (a' = ''Flo'' \<longrightarrow> range (\<lambda>x. Efid (11 * 11 ^ x)) \<inter> range (\<lambda>x. Efid (13 * 13 ^ x)) = {}) \<and>
             (a' \<noteq> ''Flo'' \<longrightarrow>
              (a' = ''David'' \<longrightarrow> range (\<lambda>x. Efid (11 * 11 ^ x)) \<inter> range (\<lambda>x. Efid (7 * 7 ^ x)) = {}) \<and>
              (a' \<noteq> ''David'' \<longrightarrow>
               (a' = ''Charly'' \<longrightarrow> range (\<lambda>x. Efid (11 * 11 ^ x)) \<inter> range (\<lambda>x. Efid (5 * 5 ^ x)) = {}) \<and>
               (a' \<noteq> ''Charly'' \<longrightarrow>
                (a' = ''Bob'' \<longrightarrow> range (\<lambda>x. Efid (11 * 11 ^ x)) \<inter> range (\<lambda>x. Efid (3 * 3 ^ x)) = {}) \<and>
                (a' \<noteq> ''Bob'' \<longrightarrow>
                 (a' = ''Alice'' \<longrightarrow> range (\<lambda>x. Efid (11 * 11 ^ x)) \<inter> range (\<lambda>x. Efid (2 * 2 ^ x)) = {}) \<and>
                 (a' \<noteq> ''Alice'' \<longrightarrow>
                  ''Eve'' \<noteq> a' \<longrightarrow> range (\<lambda>x. Efid (11 * 11 ^ x)) \<inter> range (\<lambda>x. Efid (17 * 17 ^ x)) = {}))))))) \<and>
        (a \<noteq> ''Eve'' \<longrightarrow>
         (a = ''David'' \<longrightarrow>
          (\<forall>a'\<in>InfrastructureThree.actors_graph
                 (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                   (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                        else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                             else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                  else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                       else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                            else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                 else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                   ex_locsR ex_efidsR ex_knosR).
              (a' = ''Flo'' \<longrightarrow> range (\<lambda>x. Efid (7 * 7 ^ x)) \<inter> range (\<lambda>x. Efid (13 * 13 ^ x)) = {}) \<and>
              (a' \<noteq> ''Flo'' \<longrightarrow>
               (a' = ''Eve'' \<longrightarrow> range (\<lambda>x. Efid (7 * 7 ^ x)) \<inter> range (\<lambda>x. Efid (11 * 11 ^ x)) = {}) \<and>
               (a' \<noteq> ''Eve'' \<longrightarrow>
                (a' = ''Charly'' \<longrightarrow> range (\<lambda>x. Efid (7 * 7 ^ x)) \<inter> range (\<lambda>x. Efid (5 * 5 ^ x)) = {}) \<and>
                (a' \<noteq> ''Charly'' \<longrightarrow>
                 (a' = ''Bob'' \<longrightarrow> range (\<lambda>x. Efid (7 * 7 ^ x)) \<inter> range (\<lambda>x. Efid (3 * 3 ^ x)) = {}) \<and>
                 (a' \<noteq> ''Bob'' \<longrightarrow>
                  (a' = ''Alice'' \<longrightarrow> range (\<lambda>x. Efid (7 * 7 ^ x)) \<inter> range (\<lambda>x. Efid (2 * 2 ^ x)) = {}) \<and>
                  (a' \<noteq> ''Alice'' \<longrightarrow>
                   ''David'' \<noteq> a' \<longrightarrow> range (\<lambda>x. Efid (7 * 7 ^ x)) \<inter> range (\<lambda>x. Efid (17 * 17 ^ x)) = {}))))))) \<and>
         (a \<noteq> ''David'' \<longrightarrow>
          (a = ''Charly'' \<longrightarrow>
           (\<forall>a'\<in>InfrastructureThree.actors_graph
                  (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                    (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                         else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                              else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                   else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                        else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                             else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                  else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                    ex_locsR ex_efidsR ex_knosR).
               (a' = ''Flo'' \<longrightarrow> range (\<lambda>x. Efid (5 * 5 ^ x)) \<inter> range (\<lambda>x. Efid (13 * 13 ^ x)) = {}) \<and>
               (a' \<noteq> ''Flo'' \<longrightarrow>
                (a' = ''Eve'' \<longrightarrow> range (\<lambda>x. Efid (5 * 5 ^ x)) \<inter> range (\<lambda>x. Efid (11 * 11 ^ x)) = {}) \<and>
                (a' \<noteq> ''Eve'' \<longrightarrow>
                 (a' = ''David'' \<longrightarrow> range (\<lambda>x. Efid (5 * 5 ^ x)) \<inter> range (\<lambda>x. Efid (7 * 7 ^ x)) = {}) \<and>
                 (a' \<noteq> ''David'' \<longrightarrow>
                  (a' = ''Bob'' \<longrightarrow> range (\<lambda>x. Efid (5 * 5 ^ x)) \<inter> range (\<lambda>x. Efid (3 * 3 ^ x)) = {}) \<and>
                  (a' \<noteq> ''Bob'' \<longrightarrow>
                   (a' = ''Alice'' \<longrightarrow> range (\<lambda>x. Efid (5 * 5 ^ x)) \<inter> range (\<lambda>x. Efid (2 * 2 ^ x)) = {}) \<and>
                   (a' \<noteq> ''Alice'' \<longrightarrow>
                    ''Charly'' \<noteq> a' \<longrightarrow> range (\<lambda>x. Efid (5 * 5 ^ x)) \<inter> range (\<lambda>x. Efid (17 * 17 ^ x)) = {}))))))) \<and>
          (a \<noteq> ''Charly'' \<longrightarrow>
           (a = ''Bob'' \<longrightarrow>
            (\<forall>a'\<in>InfrastructureThree.actors_graph
                   (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                     (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                          else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                               else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                    else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                         else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                              else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                   else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                     ex_locsR ex_efidsR ex_knosR).
                (a' = ''Flo'' \<longrightarrow> range (\<lambda>x. Efid (3 * 3 ^ x)) \<inter> range (\<lambda>x. Efid (13 * 13 ^ x)) = {}) \<and>
                (a' \<noteq> ''Flo'' \<longrightarrow>
                 (a' = ''Eve'' \<longrightarrow> range (\<lambda>x. Efid (3 * 3 ^ x)) \<inter> range (\<lambda>x. Efid (11 * 11 ^ x)) = {}) \<and>
                 (a' \<noteq> ''Eve'' \<longrightarrow>
                  (a' = ''David'' \<longrightarrow> range (\<lambda>x. Efid (3 * 3 ^ x)) \<inter> range (\<lambda>x. Efid (7 * 7 ^ x)) = {}) \<and>
                  (a' \<noteq> ''David'' \<longrightarrow>
                   (a' = ''Charly'' \<longrightarrow> range (\<lambda>x. Efid (3 * 3 ^ x)) \<inter> range (\<lambda>x. Efid (5 * 5 ^ x)) = {}) \<and>
                   (a' \<noteq> ''Charly'' \<longrightarrow>
                    (a' = ''Alice'' \<longrightarrow> range (\<lambda>x. Efid (3 * 3 ^ x)) \<inter> range (\<lambda>x. Efid (2 * 2 ^ x)) = {}) \<and>
                    (a' \<noteq> ''Alice'' \<longrightarrow>
                     ''Bob'' \<noteq> a' \<longrightarrow> range (\<lambda>x. Efid (3 * 3 ^ x)) \<inter> range (\<lambda>x. Efid (17 * 17 ^ x)) = {}))))))) \<and>
           (a \<noteq> ''Bob'' \<longrightarrow>
            (a = ''Alice'' \<longrightarrow>
             (\<forall>a'\<in>InfrastructureThree.actors_graph
                    (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                      (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                           else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                                else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                     else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                          else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                               else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                    else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                      ex_locsR ex_efidsR ex_knosR).
                 (a' = ''Flo'' \<longrightarrow> range (\<lambda>x. Efid (2 * 2 ^ x)) \<inter> range (\<lambda>x. Efid (13 * 13 ^ x)) = {}) \<and>
                 (a' \<noteq> ''Flo'' \<longrightarrow>
                  (a' = ''Eve'' \<longrightarrow> range (\<lambda>x. Efid (2 * 2 ^ x)) \<inter> range (\<lambda>x. Efid (11 * 11 ^ x)) = {}) \<and>
                  (a' \<noteq> ''Eve'' \<longrightarrow>
                   (a' = ''David'' \<longrightarrow> range (\<lambda>x. Efid (2 * 2 ^ x)) \<inter> range (\<lambda>x. Efid (7 * 7 ^ x)) = {}) \<and>
                   (a' \<noteq> ''David'' \<longrightarrow>
                    (a' = ''Charly'' \<longrightarrow> range (\<lambda>x. Efid (2 * 2 ^ x)) \<inter> range (\<lambda>x. Efid (5 * 5 ^ x)) = {}) \<and>
                    (a' \<noteq> ''Charly'' \<longrightarrow>
                     (a' = ''Bob'' \<longrightarrow> range (\<lambda>x. Efid (2 * 2 ^ x)) \<inter> range (\<lambda>x. Efid (3 * 3 ^ x)) = {}) \<and>
                     (a' \<noteq> ''Bob'' \<longrightarrow>
                      ''Alice'' \<noteq> a' \<longrightarrow> range (\<lambda>x. Efid (2 * 2 ^ x)) \<inter> range (\<lambda>x. Efid (17 * 17 ^ x)) = {}))))))) \<and>
            (a \<noteq> ''Alice'' \<longrightarrow>
             (\<forall>a'\<in>InfrastructureThree.actors_graph
                    (InfrastructureThree.igraph.Lgraph {(pubR, shopR)} ex_loc_assR
                      (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                           else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                                else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                     else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                          else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                               else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                    else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                      ex_locsR ex_efidsR ex_knosR).
                 (a' = ''Flo'' \<longrightarrow> range (\<lambda>x. Efid (17 * 17 ^ x)) \<inter> range (\<lambda>x. Efid (13 * 13 ^ x)) = {}) \<and>
                 (a' \<noteq> ''Flo'' \<longrightarrow>
                  (a' = ''Eve'' \<longrightarrow> range (\<lambda>x. Efid (17 * 17 ^ x)) \<inter> range (\<lambda>x. Efid (11 * 11 ^ x)) = {}) \<and>
                  (a' \<noteq> ''Eve'' \<longrightarrow>
                   (a' = ''David'' \<longrightarrow> range (\<lambda>x. Efid (17 * 17 ^ x)) \<inter> range (\<lambda>x. Efid (7 * 7 ^ x)) = {}) \<and>
                   (a' \<noteq> ''David'' \<longrightarrow>
                    (a' = ''Charly'' \<longrightarrow> range (\<lambda>x. Efid (17 * 17 ^ x)) \<inter> range (\<lambda>x. Efid (5 * 5 ^ x)) = {}) \<and>
                    (a' \<noteq> ''Charly'' \<longrightarrow>
                     (a' = ''Bob'' \<longrightarrow> range (\<lambda>x. Efid (17 * 17 ^ x)) \<inter> range (\<lambda>x. Efid (3 * 3 ^ x)) = {}) \<and>
                     (a' \<noteq> ''Bob'' \<longrightarrow>
                      (a' = ''Alice'' \<longrightarrow> range (\<lambda>x. Efid (17 * 17 ^ x)) \<inter> range (\<lambda>x. Efid (2 * 2 ^ x)) = {}) \<and>
                      (a' \<noteq> ''Alice'' \<longrightarrow> a = a')))))))))))))"
    apply (rule ballI)+
    apply (rule conjI)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_13_11, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_13_7, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_13_5, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_13_3, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_13_2, simp, simp)
     apply (rule impI)+
    apply (rule coprime_range_disjointOO)
        apply (rule coprime_13_17, simp, simp)
    apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_11_13, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_11_7, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_11_5, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
        apply (rule coprime_11_3, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
        apply (rule coprime_11_2, arith, arith)
     apply (rule impI)+
     apply (rule coprime_range_disjointOO)
    apply (rule coprime_11_17, simp, simp)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
    apply (rule coprime_range_disjointOO)
    apply (rule coprime_7_13, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_7_11, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_7_5, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_7_3, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_7_2, arith, arith)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_7_17, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_5_13, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_5_11, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_5_7, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_5_3, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_5_2, arith, arith)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_5_17, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_3_13, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_3_11, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_3_7, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_3_5, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_3_2, arith, arith)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_3_17, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_2_13, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_2_11, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_2_7, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_2_5, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_2_3, arith, arith)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_2_17, arith, arith)
     apply (rule impI)+
    apply (rule ballI)+
    apply (rule conjI)
      apply (rule impI)+
     apply (rule coprime_range_disjointOO)
    apply (rule coprime_17_13, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_17_11, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
     apply (rule coprime_range_disjointOO)
    apply (rule coprime_17_7, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_17_5, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
      apply (rule coprime_range_disjointOO)
    apply (rule coprime_17_3, arith, arith)
     apply (rule impI)+
     apply (rule conjI)
     apply (rule impI)+
     apply (rule coprime_range_disjointOO)
    apply (rule coprime_17_2, arith, arith)
     apply (rule impI)+
    by (smt (z3) InfrastructureThree.actors_graph_def InfrastructureThree.agra.simps all_not_in_conv ex_loc_assR_def insertE mem_Collect_eq)
qed


(* initially inj *)
lemma inj_efids_list_init_lem: " \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI corona_scenarioR).
       inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI corona_scenarioR) a))"
  apply (simp add: corona_scenarioR_def ex_graphR_def ex_loc_assR_def nodes_def ex_credsR_def ex_efidsR_def
             shopR_def pubR_def ex_knosR_def ex_locsR_def actors_graph_def)
  apply (rule allI)
by (simp add: inj_def)

(* Initial kgra invariant *)
lemma kgra_init_lem: "\<forall>l a. InfrastructureThree.kgra (InfrastructureThree.graphI corona_scenarioR) a l = {}"
  apply (simp add: corona_scenarioR_def ex_graphR_def ex_loc_assR_def nodes_def ex_credsR_def ex_efidsR_def
             shopR_def pubR_def)
  using ex_knosR_def by force

(* Initial finiteness invariants needed in the "pea-counting" lemma last_lem *)
lemma finite_egra_init_lem: "\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR).
       finite (InfrastructureThree.egra (InfrastructureThree.graphI corona_scenarioR) l)"
  by (simp add: corona_scenarioR_def ex_graphR_def ex_loc_assR_def nodes_def ex_credsR_def ex_efidsR_def
             shopR_def pubR_def)

lemma finite_agra_init_lem: "\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR).
       finite (InfrastructureThree.agra (InfrastructureThree.graphI corona_scenarioR) l)"
  by (simp add: corona_scenarioR_def ex_graphR_def ex_loc_assR_def nodes_def ex_credsR_def ex_efidsR_def
             shopR_def pubR_def)


text \<open>Other invariants are that the efids at egra l are in fact efids of the actors at
      that location, i.e. 
       e \<in> egra G l = (\<exists>! a \<in> agra G l.  e \<in> efid_list (cgra G a) (for InfrastructureThree))
                      .....        /\ e = efid_root (cgra G a) 
            \<close>

lemma rtrancl_imp_step: "(I \<rightarrow>\<^sub>n y) \<Longrightarrow>  (I, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* "
  by (simp add: r_into_rtrancl) 
  
lemma rtrancl_imp_two_step: "(I \<rightarrow>\<^sub>n y) \<Longrightarrow>  (y \<rightarrow>\<^sub>n z) \<Longrightarrow> (I, z) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* "
  by (simp add: converse_rtrancl_into_rtrancl)



lemma refmapThree_lem: "\<forall>s::InfrastructureThree.infrastructure.
       (corona_scenarioR, s) \<in> {(x::InfrastructureThree.infrastructure, y::InfrastructureThree.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::InfrastructureThree.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> (rmapR s, rmapR s')  \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*)"
proof (clarify, frule same_nodes, frule init_state_policy, erule state_transition_in.cases)
(* move case *)
  show "\<And>s s' G I a l l' I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a l l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       (rmapR s, rmapR s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (case_tac "l = l'")
    show "\<And>s s' G I a l l' I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a l l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       l = l' \<Longrightarrow> (rmapR s, rmapR s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
      using InfrastructureThree.move_graph_eq InfrastructureThree.ref_map_def rmapR_def by force
  next show "\<And>s s' G I a l l' I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       l' \<in> InfrastructureThree.nodes G \<Longrightarrow>
       a \<in> InfrastructureThree.actors_graph G \<Longrightarrow>
       InfrastructureThree.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.move_graph_a a l l' (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow> (rmapR s, rmapR s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* "
      apply (case_tac  "4 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI I) l) ")
       prefer 2
       apply (subgoal_tac "s = s'")
      apply force
       apply (simp add: move_graph_a_def)
      apply (smt (verit, del_insts) InfrastructureThree.delta.simps InfrastructureThree.graphI.simps InfrastructureThree.infrastructure.exhaust InfrastructureThree.move_graph_a_def InfrastructureThree.move_graph_eq)
(* *)
      apply (rule_tac I = "rmapR s" and y = "rmapR s'" in rtrancl_imp_step)
    apply (rule_tac  I = "rmapR s" and I' = "rmapR s'" and l = l and l' = l' 
                             and a = a 
 in InfrastructureTwo.state_transition_in.move)
            apply (rule refl)
         apply (simp add: InfrastructureThree.atI_def InfrastructureThree.ref_map_def InfrastructureTwo.atI_def rmapR_def)
           apply (simp add: nodes_def InfrastructureThree.atI_def InfrastructureThree.ref_map_def InfrastructureTwo.atI_def rmapR_def)
    apply (simp add: InfrastructureTwo.nodes_def)
    apply (simp add: InfrastructureThree.nodes_def InfrastructureThree.ref_map_def InfrastructureTwo.nodes_def rmapR_def)
      apply (simp add:  rmapR_def InfrastructureThree.ref_map_def InfrastructureTwo.actors_graph_def 
                        InfrastructureThree.actors_graph_def InfrastructureTwo.nodes_def InfrastructureThree.nodes_def) 
    apply (simp add: rmapR_def InfrastructureThree.ref_map_def 
                     InfrastructureThree.enables_def InfrastructureTwo.enables_def local_policiesT_def shopT_def pubT_def)
    apply (metis InfrastructureThree.delta.simps One_nat_def corona_scenarioR_def empty_iff local_policiesR_def pubR_def shopR_def)
 (* Only remaining subgoal "rmapR s' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI (rmapR s))) (InfrastructureTwo.delta (rmapR s))
    We need to provide an invariant that proves that for all reachable state the additions restrictions
    on numbers of actors is preserved.
*)
(*      apply (subgoal_tac "3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI I) l') ")
      prefer 2 
      using numbers_actors_inv_corona_scenarioR numbers_actors_inv_refl apply blast *)
(*      apply (subgoal_tac "2 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI I) l) ")
      prefer 2 
      using numbers_acors_inv_corona_scenarioR numbers_actors_inv_refl apply blast *)
    apply (simp add: InfrastructureTwo.move_graph_a_def InfrastructureThree.move_graph_a_def
                     rmapR_def InfrastructureThree.ref_map_def 
                     local_policiesT_def shopT_def pubT_def)
(* here *)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule conjI)
    apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureThree.efids_inc_ind_def) 
      apply (simp add: InfrastructureTwo.efids_cur_def InfrastructureThree.efids_cur_def
                        InfrastructureTwo.efids_inc_ind_def InfrastructureThree.efids_inc_ind_def)
      apply force
      using numbers_actors_inv_corona_scenarioR numbers_actors_inv_refl by presburger 
(*    by (simp add: InfrastructureTwo.efids_cur_def InfrastructureThree.efids_cur_def
                        InfrastructureTwo.efids_inc_ind_def InfrastructureThree.efids_inc_ind_def) *) 
qed
next show "\<And>s s' G I a l I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       (rmapR s, rmapR s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (rule rtrancl_imp_step, rule_tac I =  "rmapR s" and I' = "rmapR s'" and l = l  and a = a  
        in InfrastructureTwo.state_transition_in.get, 
        rule refl, simp add: rmapR_def ref_map_def atI_def InfrastructureTwo.atI_def
        local_policiesT_def InfrastructureTwo.nodes_def shopT_def pubT_def)
    show "\<And>s s' G I a l I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI (rmapR s))"
      apply (simp add: rmapR_def local_policiesT_def ref_map_def)
      using InfrastructureTwo.nodes_def InfrastructureThree.nodes_def by fastforce
  next show "\<And>s s' G I a l I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       InfrastructureTwo.enables (rmapR s) l (Actor a) get"
   proof (simp add: rmapR_def ref_map_def nodes_def enables_def InfrastructureTwo.enables_def
              local_policiesT_def InfrastructureTwo.nodes_def shopT_def pubT_def)
     show "\<And>s s' G I a l I'.
       (corona_scenarioR, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       {x. \<exists>y. (x, y) \<in> InfrastructureThree.gra (InfrastructureThree.graphI corona_scenarioR) \<or>
               (y, x) \<in> InfrastructureThree.gra (InfrastructureThree.graphI corona_scenarioR)} =
       {x. \<exists>y. (x, y) \<in> InfrastructureThree.gra (InfrastructureThree.graphI I) \<or>
               (y, x) \<in> InfrastructureThree.gra (InfrastructureThree.graphI I)} \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta I \<Longrightarrow>
       s = I \<Longrightarrow>
       s' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra (InfrastructureThree.graphI I))
          (InfrastructureThree.agra (InfrastructureThree.graphI I))
          (InfrastructureThree.cgra (InfrastructureThree.graphI I))
          (InfrastructureThree.lgra (InfrastructureThree.graphI I))
          (InfrastructureThree.egra (InfrastructureThree.graphI I))
          ((InfrastructureThree.kgra (InfrastructureThree.graphI I))
           (a := (InfrastructureThree.kgra (InfrastructureThree.graphI I) a)
              (l := InfrastructureThree.agra (InfrastructureThree.graphI I) l \<times>
                    InfrastructureThree.egra (InfrastructureThree.graphI I) l))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureThree.graphI I\<^esub> l \<Longrightarrow>
       \<exists>y. (l, y) \<in> InfrastructureThree.gra (InfrastructureThree.graphI I) \<or>
           (y, l) \<in> InfrastructureThree.gra (InfrastructureThree.graphI I) \<Longrightarrow>
       \<exists>x\<in>InfrastructureThree.delta I (InfrastructureThree.graphI I) l. case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra (InfrastructureThree.graphI I))
          (InfrastructureThree.agra (InfrastructureThree.graphI I))
          (InfrastructureThree.cgra (InfrastructureThree.graphI I))
          (InfrastructureThree.lgra (InfrastructureThree.graphI I))
          (InfrastructureThree.egra (InfrastructureThree.graphI I))
          ((InfrastructureThree.kgra (InfrastructureThree.graphI I))
           (a := (InfrastructureThree.kgra (InfrastructureThree.graphI I) a)
              (l := InfrastructureThree.agra (InfrastructureThree.graphI I) l \<times>
                    InfrastructureThree.egra (InfrastructureThree.graphI I) l))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       l \<noteq> Location (Suc 0) \<longrightarrow> l = Location 0"
        by (metis InfrastructureThree.delta.simps One_nat_def corona_scenarioR_def empty_iff local_policiesR_def pubR_def shopR_def)
    qed
  next show "\<And>s s' G I a l I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureThree.nodes G \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.igraph.Lgraph (InfrastructureThree.gra G) (InfrastructureThree.agra G)
          (InfrastructureThree.cgra G) (InfrastructureThree.lgra G) (InfrastructureThree.egra G)
          ((InfrastructureThree.kgra G)
           (a := (InfrastructureThree.kgra G a)
              (l := {(x, y). x \<in> InfrastructureThree.agra G l \<and> y \<in> InfrastructureThree.egra G l}))))
        (InfrastructureThree.delta I) \<Longrightarrow>
       rmapR s' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI (rmapR s)))
          (InfrastructureTwo.agra (InfrastructureTwo.graphI (rmapR s)))
          (InfrastructureTwo.cgra (InfrastructureTwo.graphI (rmapR s)))
          (InfrastructureTwo.lgra (InfrastructureTwo.graphI (rmapR s)))
          (InfrastructureTwo.egra (InfrastructureTwo.graphI (rmapR s)))
          ((InfrastructureTwo.kgra (InfrastructureTwo.graphI (rmapR s)))
           (a := (InfrastructureTwo.kgra (InfrastructureTwo.graphI (rmapR s)) a)
              (l := {(x, y).
                     x \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI (rmapR s)) l \<and>
                     y \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI (rmapR s)) l}))))
        (InfrastructureTwo.delta (rmapR s))"
by (simp add: rmapR_def ref_map_def)
qed
next show "\<And>s s' G I a l I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       (rmapR s, rmapR s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (rule rtrancl_imp_step, rule_tac I = "rmapR s" and I' = "rmapR s'" and l = l  
                             and a = a 
 in InfrastructureTwo.state_transition_in.put, rule refl, simp add: rmapR_def ref_map_def atI_def InfrastructureTwo.atI_def
     ,simp add: rmapR_def ref_map_def nodes_def enables_def InfrastructureTwo.enables_def
              local_policiesT_def InfrastructureTwo.nodes_def shopT_def pubT_def)
    show "\<And>s s' G I a l I'.
       (corona_scenarioR, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       {x. \<exists>y. (x, y) \<in> InfrastructureThree.gra (InfrastructureThree.graphI corona_scenarioR) \<or>
               (y, x) \<in> InfrastructureThree.gra (InfrastructureThree.graphI corona_scenarioR)} =
       {x. \<exists>y. (x, y) \<in> InfrastructureThree.gra (InfrastructureThree.graphI I) \<or>
               (y, x) \<in> InfrastructureThree.gra (InfrastructureThree.graphI I)} \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta I \<Longrightarrow>
       s = I \<Longrightarrow>
       s' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureThree.graphI I\<^esub> l \<Longrightarrow>
       \<exists>x\<in>InfrastructureThree.delta I (InfrastructureThree.graphI I) l. case x of (p, e) \<Rightarrow> put \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       l \<noteq> Location (Suc 0) \<longrightarrow> l = Location 0"
      using all_not_in_conv corona_scenarioR_def local_policiesR_def pubR_def shopR_def by fastforce
  next show "\<And>s s' G I a l I'.
       (corona_scenarioR, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureThree.nodes (InfrastructureThree.graphI corona_scenarioR) =
       InfrastructureThree.nodes (InfrastructureThree.graphI s) \<Longrightarrow>
       InfrastructureThree.delta corona_scenarioR = InfrastructureThree.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureThree.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureThree.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureThree.infrastructure.Infrastructure
        (InfrastructureThree.put_graph_efid a l (InfrastructureThree.graphI I)) (InfrastructureThree.delta I) \<Longrightarrow>
       rmapR s' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.put_graph_efid a l (InfrastructureTwo.graphI (rmapR s))) (InfrastructureTwo.delta (rmapR s))"
      apply (simp add: rmapR_def ref_map_def)
    apply (simp add: put_graph_efid_def InfrastructureTwo.put_graph_efid_def)
      apply (rule conjI)
       apply (rule ext, simp add: InfrastructureThree.efids_inc_ind_def InfrastructureTwo.efids_inc_ind_def)
       apply (rule ext, simp)
      apply (rule impI)
      by (simp add: InfrastructureThree.efids_cur_def InfrastructureTwo.efids_cur_def
                       InfrastructureThree.efids_inc_ind_def InfrastructureTwo.efids_inc_ind_def)
qed
qed


theorem refmapThree: "corona_KripkeT \<sqsubseteq>\<^sub>rmapR corona_KripkeR"
proof (rule strong_mt'', simp add: corona_KripkeR_def corona_KripkeT_def corona_statesR_def corona_statesT_def state_transition_refl_def, rule conjI)
  show "IcoronaR \<subseteq> {I. (corona_scenarioR, I) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*}"
    using IcoronaR_def by fastforce
next show "IcoronaT \<subseteq> {I. (corona_scenarioT, I) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*} \<and>
    rmapR ` IcoronaR \<subseteq> IcoronaT \<and>
    (\<forall>s. (\<exists>s0\<in>IcoronaR. (s0, s) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*) \<longrightarrow>
         (\<forall>s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (rmapR s, rmapR s') \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*)) "
     apply (rule conjI)
    using IcoronaT_def apply blast
    apply (rule conjI)
     apply (simp add: rmapR_def ref_map_def IcoronaT_def IcoronaR_def corona_scenarioT_def corona_scenarioR_def
                      ex_graphT_def ex_graphR_def pubT_def pubR_def  ex_loc_assR_def
            ex_loc_assT_def ext ex_credsT_def  ex_credsR_def ex_locsT_def ex_locsR_def 
            ex_efidsR_def ex_efidsT_def shopT_def shopR_def
            ex_knosR_def ex_knosT_def repl_efr_def)
    using IcoronaR_def InfrastructureTwo.state_transition_infra_def InfrastructureThree.state_transition_infra_def refmapThree_lem by auto
qed

lemma step1: "corona_scenarioR  \<rightarrow>\<^sub>n corona_scenarioR'"
  oops

lemma step1r: "corona_scenarioR  \<rightarrow>\<^sub>n* corona_scenarioR'"
  oops

(* These lemmas are all now on unreachable states
lemma step2: "corona_scenarioR'  \<rightarrow>\<^sub>n corona_scenarioR''"
  oops

lemma step2r: "corona_scenarioR'  \<rightarrow>\<^sub>n* corona_scenarioR''"
  oops

lemma step3: "corona_scenarioR''  \<rightarrow>\<^sub>n corona_scenarioR'''"
  oops

lemma step3r: "corona_scenarioR''  \<rightarrow>\<^sub>n* corona_scenarioR'''"
  oops

lemma step4: "corona_scenarioR'''  \<rightarrow>\<^sub>n corona_scenarioR''''"
  oops

lemma step4r: "corona_scenarioR'''  \<rightarrow>\<^sub>n* corona_scenarioR''''"
  oops
*)

(*
lemma corona_refR: "[\<N>\<^bsub>(IcoronaR,scoronaR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaR,scoronaR)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaR,CoronaR')\<^esub>, \<N>\<^bsub>(CoronaR',CoronaR'')\<^esub>,  \<N>\<^bsub>(CoronaR'',CoronaR''')\<^esub>, \<N>\<^bsub>(CoronaR''',scoronaR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaR,scoronaR)\<^esup>)"
  oops

lemma att_coronaR: "\<turnstile>([\<N>\<^bsub>(IcoronaR,CoronaR')\<^esub>, \<N>\<^bsub>(CoronaR',CoronaR'')\<^esub>,  \<N>\<^bsub>(CoronaR'',CoronaR''')\<^esub>, \<N>\<^bsub>(CoronaR''',scoronaR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaR,scoronaR)\<^esup>)"
  oops
*)

lemma corona_abs_attR: "\<turnstile>\<^sub>V([\<N>\<^bsub>(IcoronaR,scoronaR)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaR,scoronaR)\<^esup>)"
  oops

lemma corona_attR: "corona_KripkeR \<turnstile> EF {x. \<exists> n. \<not>(global_policyR'' x (Efid n))}"
  oops

theorem corona_EFR: "corona_KripkeR \<turnstile> EF scoronaR"
  oops

theorem corona_ATT: "\<exists> A. \<turnstile> A \<and> attack A = (IcoronaR,scoronaR)"
  oops

theorem corona_EFR': "corona_KripkeR \<turnstile> EF scoronaR"
  oops

  thm contrapos_corr

(* As at level Two, global_policyR'' holds *)
lemma kgra_disj_imp_not_identifiable: 
"''Eve'' \<in>  actors_graph  (graphI I) \<Longrightarrow>
\<exists> l \<in> nodes (graphI I). \<exists> l' \<in> nodes (graphI I). l \<noteq> l' \<Longrightarrow>
(\<forall> a \<in> actors_graph  (graphI I).
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
         (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {})))
\<Longrightarrow> global_policyR'' I eid "
  apply (simp add: global_policyR''_def identifiableR'_def)
  apply (erule bexE)+
  apply (subgoal_tac "{(Id, Eid).
            (\<forall>x\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
                (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' x) \<and>
            Id \<noteq> ''Eve'' \<and> Eid = eid} = {}")
   apply (erule ssubst)
   apply (simp add: is_singleton_def)
  by (smt (verit, ccfv_threshold) IntI case_prodI2 case_prod_conv empty_Collect_eq empty_iff split_part)


(* Proof idea for global_policyR and global_policyR' is again that all intersections are empty
   and thus for any subset of intersections we have that policy holds (the single set being the
   special care global_policyR')
lemma global_policy_strength: "global_policyR I eid \<Longrightarrow> global_policyR'' I eid"

  using global_policyR''_def global_policyR_def by blast
*)
thm bspec
thm ballI

lemma set_spec: "\<forall> L\<subseteq> S. P L \<Longrightarrow> L' \<subseteq> S \<Longrightarrow> P L'"
  by simp

lemma set_allI:  "(\<And> L'. L' \<subseteq> S \<Longrightarrow> P L') \<Longrightarrow> \<forall> L\<subseteq> S. P L "
  by simp

(*
lemma global_policy_strengthO: "global_policyR I eid \<Longrightarrow> global_policyR' I eid"
proof (simp add: global_policyR_def global_policyR'_def)
  show "\<forall>L\<subseteq>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<not> identifiableR' eid
           (\<Inter> (InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' ` L) - {(x, y). x = ''Eve''}) \<Longrightarrow>
    \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<not> identifiableR' eid (InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l - {(x, y). x = ''Eve''})"
    apply (rule ballI)
    apply (drule_tac L' = "{l}" in set_spec)
    by simp+
qed

lemma global_policy_strengthOO: "global_policyR'' I eid \<Longrightarrow> global_policyR' I eid \<Longrightarrow> global_policyR I eid"
proof (simp add: global_policyR_def global_policyR'_def global_policyR''_def)
  show "\<not> identifiableR' eid
        (\<Inter> (InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' `
             InfrastructureThree.nodes (InfrastructureThree.graphI I)) -
         {(x, y). x = ''Eve''}) \<Longrightarrow>
    \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<not> identifiableR' eid
           (InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l - {(x, y). x = ''Eve''}) \<Longrightarrow>
    \<forall>L\<subseteq>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<not> identifiableR' eid
           (\<Inter> (InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' ` L) - {(x, y). x = ''Eve''})"
    apply (rule set_allI)
    apply (unfold identifiableR'_def)
    apply (simp add: is_singleton_def)
    apply (rule allI)+


  oops
*)


(* We can already establish non-identifiability for subsets L with more than 2 elements.
   This should follow simply from disjointness of the kgra set intersections for all pairs of 
   locations. *)
lemma card_two_two_not_eq_elem: "2 \<le> card L \<Longrightarrow> \<exists>l\<in>L. \<exists>l'\<in>L. l \<noteq> l'"
  apply (subgoal_tac "L \<noteq> {}")
   prefer 2
  apply force
  apply (subgoal_tac "\<exists> x. x \<in> L")
  prefer 2
   apply auto[1]
  apply (erule exE)
  apply (subgoal_tac "L - {x} \<noteq> {}")
  prefer 2
   apply (metis Suc_n_not_le_n card.empty card.infinite card_Suc_Diff1 not_numeral_le_zero numeral_2_eq_2)
  apply (subgoal_tac "\<exists> y. y \<in> (L - {x})")
   prefer 2
   apply auto[1]
  apply (rule_tac x = x in bexI)
  apply (erule exE)
   apply (rule_tac x = y in bexI)
    apply force
   apply simp
  by assumption


lemma all_kgra_disj_imp_greater_two_inv: "(\<forall> a \<in> actors_graph (graphI I). 
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
      (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {}))) \<Longrightarrow>
      L \<subseteq> nodes(graphI I)  \<Longrightarrow> card L \<ge> 2 \<Longrightarrow> 
      ''Eve'' \<in> actors_graph (graphI I) \<Longrightarrow>
      (\<not>(identifiableR' eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L))
                          - {(x,y). x = ''Eve''})))"
  apply (simp add: identifiableR'_def) 
  apply (subgoal_tac " {(Id, Eid).
         (\<forall>x\<in>L. (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' x) \<and>
         Id \<noteq> ''Eve'' \<and> Eid = eid} = {}")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (simp add: is_singleton_def)
  apply (rule equalityI)
   prefer 2
   apply simp
  apply (rule subsetI)
  apply simp
  apply (case_tac x)
  apply simp
  apply (subgoal_tac "\<exists> l \<in> L. (\<exists> l' \<in> L. l \<noteq> l')")
   apply (erule bexE)+
  apply (erule conjE)
   apply (frule_tac x = l in bspec, assumption)
   apply (drule_tac x = l' in bspec, assumption)
   apply (drule_tac x = "''Eve''" in bspec)
  prefer 2
    apply (meson disjoint_iff in_mono)
   apply assumption
by (erule card_two_two_not_eq_elem)

lemma empty_kgra: "kgra (graphI I)(''Eve'')` {} = {}"
  by (rule image_empty)

(* The remaining case: empty or just one l *)
lemma "\<Inter> ({{}}) = {}"
  by (rule cInf_singleton)

lemma empty_minus: "({} - {(x, y). x = ''Eve''}) = {}"
  by (rule empty_Diff)

lemma "card {} = 0"
  by (rule card.empty)

lemma "finite S \<Longrightarrow> I \<notin> S \<Longrightarrow> card (insert I S) = Suc (card S)"
  by(rule card_insert_disjoint)

lemma "card {l :: location} = 1"
  by simp

lemma "(l:: location) \<in> L \<Longrightarrow> card L < (2 :: nat) \<Longrightarrow> L = {l}"
   apply (subgoal_tac "card L = 1")
    apply (metis card_1_singletonE empty_iff insertE)
   apply (subgoal_tac "card L > 0")
   apply linarith
  apply (subgoal_tac "finite L")
  using card_gt_0_iff apply blast
  oops


lemma all_kgra_disj_imp_less_two_inv: 
     "L \<subseteq> nodes(graphI I)  \<Longrightarrow> card L < 2 \<Longrightarrow> 
      ''Eve'' \<in> actors_graph (graphI I) \<Longrightarrow> 0 < card L \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       {(Id, Eid).
        (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq>
       {} \<longrightarrow>
       2 \<le> card {(Id, Eid).
                  (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and>
                  Id \<noteq> ''Eve'' \<and> Eid = eid} \<Longrightarrow>
      (\<not>(identifiableR' eid 
               (((\<Inter> (kgra(graphI I)(''Eve'')`L)
                          - {(x,y). x = ''Eve''})))))"
  apply (subgoal_tac "finite L")
  prefer 2
  using card_gt_0_iff apply blast
  apply (subgoal_tac "card L = 1")
   prefer 2
   apply linarith
  apply (subgoal_tac "\<exists> l. L = {l}")
   prefer 2
   apply (meson card_1_singletonE)
  apply (erule exE)
  apply simp
  apply (simp add: identifiableR'_def)
  apply (subgoal_tac "{(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} = {} 
\<or>
card({(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid}) \<ge> 2")
   apply (erule disjE)
  apply (rotate_tac -1)
  apply (erule ssubst)
  apply (simp add: is_singleton_def)+
   apply force
  apply (case_tac "{(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} = {}")
   apply simp
  apply (rule disjI2)
by simp

(* putting the previous two cases together *)
lemma all_kgra_disj_imp_inv: "''Eve'' \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
     (\<forall> a \<in> actors_graph (graphI I).
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
      (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {}))) \<Longrightarrow>
     (\<forall> l \<in> nodes (graphI I). {(Id, Eid).
          (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq>
         {} \<longrightarrow>
     ( 2 \<le> card {(Id, Eid).
                    (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and>
                    Id \<noteq> ''Eve'' \<and> Eid = eid})) \<Longrightarrow> global_policyR I eid"
  apply (unfold global_policyR_def)
  apply (rule allI)
  apply (rule impI)+
  apply (subgoal_tac "(0 < card L \<and> card L < 2) \<or> card L \<ge> 2")
   prefer 2
   apply arith
  apply (erule disjE)
  apply (rule all_kgra_disj_imp_less_two_inv, assumption, simp, assumption, simp, assumption)
  using all_kgra_disj_imp_greater_two_inv by presburger

(* *)

(* Should be the same as the global_policy and the intersection should follow *)
lemma global_policy_valid: "(corona_scenarioR  \<rightarrow>\<^sub>n* y) \<Longrightarrow>  global_policyR y eid"
  apply (rule all_kgra_disj_imp_inv)
  apply (simp add: InfrastructureThree.state_transition_in_refl_def all_corona_actors corona_actorsR_def)
   apply (rule theoremAOO, simp add: state_transition_in_refl_def)
       apply (simp add: kgra_init_lem)
  apply (simp add: inj_efids_list_init_lem)
  apply (simp add: actors_unique_init_lem)
  apply (simp add: range_disjoint_corona_scenarioR)
   apply (simp add: efid_eq_efid_cur_corona_scenarioR)
  apply (rule last_lemOO)
           apply (simp add: state_transition_in_refl_def)
  using kgra_init_lem apply blast
  using range_disjoint_corona_scenarioR apply blast
  apply (smt (verit, best) InfrastructureThree.efids_cur_in_efids_listO disjoint_iff inj_onI range_disjoint_corona_scenarioR)
  using inj_efids_list_init_lem apply blast
  using actors_unique_init_lem apply blast
  using local.isthere_lem00 apply blast
    apply (rule finite_egra_init_lem) 
   apply (rule finite_agra_init_lem)
  using numbers_actors_inv_corona_scenarioR by blast 


lemma  AG_all_sO_n: "(\<forall>y. (x,y)\<in> {(x,y). state_transition_in x y}\<^sup>* \<longrightarrow> y \<in> s) \<Longrightarrow> x \<in> AG s"
  apply (rule AG_all_sO)
  by (smt (verit) Collect_cong InfrastructureThree.state_transition_infra_def split_cong state_transition_refl_def)

theorem RR_cycle_succeeds: "corona_KripkeR \<turnstile> AG {x. \<forall> n. global_policyR x (Efid n)}"
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (simp add: corona_KripkeR_def IcoronaR_def corona_statesR_def)
  apply (rule conjI)
  using EF_lem2a EF_step_star_rev apply blast
  apply (rule AG_all_sO_n)
  apply (rule allI)
  apply (rule impI)
  apply (rule CollectI, rule allI)
  apply (rule global_policy_valid)
by (simp add: state_transition_in_refl_def)
 

end

(* Generalisation of RR_cycle_succeeds *)
(* First need to generalise a few lemmas *)

(* For the generalisation, we need to redefine the global policy at global level*)
definition identifiable :: "[efid, (identity * efid)set] \<Rightarrow> bool"
  where \<open>identifiable eid A \<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> A \<and> Eid = eid}\<close>


(* This has the same meaning:
  thm CoronaAppThree.scenarioCoronaThree.global_policyR_def 
but for practicality we redefine the global policy with a global name *)

definition global_policy :: "[infrastructure, efid] \<Rightarrow> bool"
where \<open>global_policy I eid \<equiv>  
             \<forall> L. 0 < card L \<longrightarrow> L \<subseteq> nodes(graphI I) \<longrightarrow> (\<not>(identifiable eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L)
                          - {(x,y). x = ''Eve''}))))\<close>

lemma all_kgra_disj_imp_greater_two_inv_gen: "(\<forall> a \<in> actors_graph (graphI I). 
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
      (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {}))) \<Longrightarrow>
      L \<subseteq> nodes(graphI I)  \<Longrightarrow> card L \<ge> 2 \<Longrightarrow> 
      ''Eve'' \<in> actors_graph (graphI I) \<Longrightarrow>
      (\<not>(identifiable eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L))
                          - {(x,y). x = ''Eve''})))"
  apply (simp add: identifiable_def) 
  apply (subgoal_tac " {(Id, Eid).
         (\<forall>x\<in>L. (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' x) \<and>
         Id \<noteq> ''Eve'' \<and> Eid = eid} = {}")
   apply (rotate_tac -1)
   apply (erule ssubst)
   apply (simp add: is_singleton_def)
  apply (rule equalityI)
   prefer 2
   apply simp
  apply (rule subsetI)
  apply simp
  apply (case_tac x)
  apply simp
  apply (subgoal_tac "\<exists> l \<in> L. (\<exists> l' \<in> L. l \<noteq> l')")
   apply (erule bexE)+
  apply (erule conjE)
   apply (frule_tac x = l in bspec, assumption)
   apply (drule_tac x = l' in bspec, assumption)
   apply (drule_tac x = "''Eve''" in bspec)
  prefer 2
    apply (meson disjoint_iff in_mono)
   apply assumption
by (erule CoronaAppThree.scenarioCoronaThree.card_two_two_not_eq_elem)



lemma all_kgra_disj_imp_less_two_inv_gen: 
     "L \<subseteq> nodes(graphI I)  \<Longrightarrow> card L < 2 \<Longrightarrow> 
      ''Eve'' \<in> actors_graph (graphI I) \<Longrightarrow> 0 < card L \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       {(Id, Eid).
        (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq>
       {} \<longrightarrow>
       2 \<le> card {(Id, Eid).
                  (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and>
                  Id \<noteq> ''Eve'' \<and> Eid = eid} \<Longrightarrow>
      (\<not>(identifiable eid 
               (((\<Inter> (kgra(graphI I)(''Eve'')`L)
                          - {(x,y). x = ''Eve''})))))"
  apply (subgoal_tac "finite L")
  prefer 2
  using card_gt_0_iff apply blast
  apply (subgoal_tac "card L = 1")
   prefer 2
   apply linarith
  apply (subgoal_tac "\<exists> l. L = {l}")
   prefer 2
   apply (meson card_1_singletonE)
  apply (erule exE)
  apply simp
  apply (simp add: identifiable_def)
  apply (subgoal_tac "{(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} = {} 
\<or>
card({(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid}) \<ge> 2")
   apply (erule disjE)
  apply (rotate_tac -1)
  apply (erule ssubst)
  apply (simp add: is_singleton_def)+
   apply force
  apply (case_tac "{(Id, Eid).
     (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} = {}")
   apply simp
  apply (rule disjI2)
by simp


lemma all_kgra_disj_imp_inv_gen: "''Eve'' \<in> InfrastructureThree.actors_graph (InfrastructureThree.graphI I) \<Longrightarrow>
     (\<forall> a \<in> actors_graph (graphI I).
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
      (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {}))) \<Longrightarrow>
     (\<forall> l \<in> nodes (graphI I). {(Id, Eid).
          (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and> Id \<noteq> ''Eve'' \<and> Eid = eid} \<noteq>
         {} \<longrightarrow>
     ( 2 \<le> card {(Id, Eid).
                    (Id, Eid) \<in> InfrastructureThree.kgra (InfrastructureThree.graphI I) ''Eve'' l \<and>
                    Id \<noteq> ''Eve'' \<and> Eid = eid})) \<Longrightarrow> global_policy I eid"
  apply (unfold global_policy_def)
  apply (rule allI)
  apply (rule impI)+
  apply (subgoal_tac "(0 < card L \<and> card L < 2) \<or> card L \<ge> 2")
   prefer 2
   apply arith
  apply (erule disjE)
  apply (rule all_kgra_disj_imp_less_two_inv_gen, assumption, simp, assumption, simp, assumption)
  using all_kgra_disj_imp_greater_two_inv_gen by presburger

(* Now, we can reprove the general validity of the global policy (called global_policyR in the locale.
   All the locale lemmas that proved specific required lemmas about the finite infrastructure example
   used in the locale, lead now to a list of assumptions here in the generalised theorem. 
   The first theorem global_policy_valid shows the validity of the global policy for all states.
   This is then generalised into the corresponding AG property below in theorem RR_cycle_succeeds_gen *)
lemma global_policy_valid: "(I  \<rightarrow>\<^sub>n* y) \<Longrightarrow>  
''Eve'' \<in> actors_graph (graphI I) \<Longrightarrow>
\<forall>l a. InfrastructureThree.kgra (InfrastructureThree.graphI I) a l = {} \<Longrightarrow>
\<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
       inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<Longrightarrow>
\<forall>a l l'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
       a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
       a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l' \<longrightarrow> l = l' \<Longrightarrow>
 \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
       \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI I).
          a \<noteq> a' \<longrightarrow>
          range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)) \<inter>
          range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI I) a')) =
          {} \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI I) l.
          \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI I) l.
             e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a) \<Longrightarrow>
\<forall>a l. l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI I) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI I) l \<longrightarrow>
          InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI I) a)
          \<in> InfrastructureThree.egra (InfrastructureThree.graphI I) l \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       finite (InfrastructureThree.egra (InfrastructureThree.graphI I) l) \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       finite (InfrastructureThree.agra (InfrastructureThree.graphI I) l) \<Longrightarrow>
\<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI I).
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI I) l) \<Longrightarrow>
global_policy y (Efid n)"
  apply (rule all_kgra_disj_imp_inv_gen)
  using InfrastructureThree.same_actors InfrastructureThree.state_transition_in_refl_def apply fastforce
  thm theoremAOO
   apply (rule theoremAOO)
  apply (simp add: state_transition_in_refl_def)
       apply (assumption)+
  apply (rule last_lemOO)
           apply (simp add: state_transition_in_refl_def)
  apply assumption+
        apply (smt (verit, ccfv_SIG) InfrastructureThree.efids_cur_in_efids_listO disjoint_iff inj_on_def)
  by assumption+

(* Simply embedding the previous theorem into the CTL form as an AG formula 
   Effectively, the first part just dels with the AG deconstruction -- afterward global_policy_gen is
   applied and the assumptions discharged. *)
theorem RR_cycle_succeeds_gen: "I \<noteq> {} \<Longrightarrow> 
  \<forall> x \<in> I. ''Eve'' \<in> actors_graph (graphI x) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>l a. InfrastructureThree.kgra (InfrastructureThree.graphI x) a l = {}) \<Longrightarrow>
(\<forall> x \<in> I. \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI x).
       inj (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI x) a))) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>a l l'.
       l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI x) \<longrightarrow>
       a \<in> InfrastructureThree.agra (InfrastructureThree.graphI x) l \<longrightarrow>
       a \<in> InfrastructureThree.agra (InfrastructureThree.graphI x) l' \<longrightarrow> l = l') \<Longrightarrow>
  (\<forall> x \<in> I. \<forall>a\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI x).
       \<forall>a'\<in>InfrastructureThree.actors_graph (InfrastructureThree.graphI x).
          a \<noteq> a' \<longrightarrow>
          range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI x) a)) \<inter>
          range (InfrastructureThree.efids_list (InfrastructureThree.cgra (InfrastructureThree.graphI x) a')) =
          {}) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI x).
       \<forall>e\<in>InfrastructureThree.egra (InfrastructureThree.graphI x) l.
          \<exists>a\<in>InfrastructureThree.agra (InfrastructureThree.graphI x) l.
             e = InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI x) a)) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>a l. l \<in> InfrastructureThree.nodes (InfrastructureThree.graphI x) \<longrightarrow>
          a \<in> InfrastructureThree.agra (InfrastructureThree.graphI x) l \<longrightarrow>
          InfrastructureThree.efids_cur (InfrastructureThree.cgra (InfrastructureThree.graphI x) a)
          \<in> InfrastructureThree.egra (InfrastructureThree.graphI x) l) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI x).
       finite (InfrastructureThree.egra (InfrastructureThree.graphI x) l)) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI x).
       finite (InfrastructureThree.agra (InfrastructureThree.graphI x) l)) \<Longrightarrow>
 (\<forall> x \<in> I. \<forall>l\<in>InfrastructureThree.nodes (InfrastructureThree.graphI x).
       3 \<le> card (InfrastructureThree.agra (InfrastructureThree.graphI x) l)) \<Longrightarrow>
                  ((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>n* s)} I  \<turnstile> AG {x. \<forall> n. global_policy x (Efid n)}))"
  apply (simp add: check_def)
  apply (rule subsetI)
  apply simp
  apply (rule conjI)
  using InfrastructureThree.state_transition_in_refl_def apply auto[1]
  apply (rule CoronaAppThree.scenarioCoronaThree.AG_all_sO_n)
  apply (rule allI)
  apply (rule impI)
  apply (rule CollectI)
  apply (rule allI)
  apply (rule global_policy_valid)
  apply (simp add: InfrastructureThree.state_transition_in_refl_def)
  by simp+

end
