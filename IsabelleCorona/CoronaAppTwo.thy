theory CoronaAppTwo
  imports InfrastructureTwo
begin
locale scenarioCoronaTwo = scenarioCoronaOne +

fixes corona_actorsT :: "identity set"
defines corona_actorsT_def: "corona_actorsT \<equiv> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}"

fixes corona_locationsT :: "location set"
defines corona_locationsT_def: "corona_locationsT \<equiv> {Location 0, Location 1}"
fixes pubT :: "location"
defines pubT_def: "pubT \<equiv> Location 0"
fixes shopT :: "location"
defines shopT_def: "shopT \<equiv> Location 1"

(* not relevant any more. It was made for earlier versions where the intersection happened
   implicitly in the semantics. 
fixes identifiable :: "[infrastructure,actor,efid, location] \<Rightarrow> bool"
defines identifiable_def: "identifiable I a eid l\<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> kgra (graphI I) a l \<and> Eid = eid}"
fixes global_policy :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy_def: "global_policy I eid \<equiv>  (\<exists> l. \<not>(identifiable I (Actor ''Eve'') eid l))"
*)

fixes identifiableT' :: "[efid, (identity * efid)set] \<Rightarrow> bool"
defines identifiableT'_def: "identifiableT' eid A \<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> A \<and> Eid = eid}"

fixes global_policyT'' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyT''_def: "global_policyT'' I eid \<equiv>  
             \<not>(identifiableT' eid 
                ((\<Inter> (kgra(graphI I)(''Eve'')`(nodes(graphI I))))
                 - {(x,y). x = ''Eve''}))"

fixes global_policyT :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyT_def: "global_policyT I eid \<equiv>  
             \<forall> L. L \<subseteq> nodes(graphI I) \<longrightarrow> (\<not>(identifiableT' eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L))
                          - {(x,y). x = ''Eve''})))"

fixes ex_credsT :: "identity \<Rightarrow> efidlist"
defines ex_credsT_def: 
          "ex_credsT \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 0 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"

fixes ex_credsT' :: "identity \<Rightarrow> efidlist"
defines ex_credsT'_def: 
          "ex_credsT' \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 1 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"

fixes ex_credsT'' :: "identity \<Rightarrow> efidlist"
defines ex_credsT''_def: 
          "ex_credsT'' \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 1 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 1 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"

fixes ex_locsT :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locsT \<equiv> (\<lambda> x. ('''',{}))"

fixes ex_loc_assT :: "location \<Rightarrow> identity set"
defines ex_loc_assT_def: "ex_loc_assT \<equiv>
          (\<lambda> x. if x = pubT then {''Alice'', ''Bob'', ''Eve''}  
                 else (if x = shopT then {''Charly'', ''David'', ''Flo''} 
                       else {}))"
fixes ex_loc_assT' :: "location \<Rightarrow> identity set"
defines ex_loc_assT'_def: "ex_loc_assT' \<equiv>
          (\<lambda> x. if x = pubT then {''Alice'', ''Eve''}  
                 else (if x = shopT then { ''Bob'', ''Charly'', ''David'', ''Flo''} 
                       else {}))"
fixes ex_loc_assT'' :: "location \<Rightarrow> identity set"
defines ex_loc_assT''_def: "ex_loc_assT'' \<equiv>
          (\<lambda> x. if x = pubT then {''Alice''}  
                 else (if x = shopT then {''Eve'', ''Bob'', ''Charly'', ''David'', ''Flo''} 
                       else {}))"

fixes ex_efidsT :: "location \<Rightarrow> efid set"
defines ex_efidsT_def: "ex_efidsT \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 2, Efid 3, Efid 11}
                else (if x = shopT then {Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_efidsT' :: "location \<Rightarrow> efid set"
defines ex_efidsT'_def: "ex_efidsT' \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 2, Efid 11}
                else (if x = shopT then {Efid 9, Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_efidsT'' :: "location \<Rightarrow> efid set"
defines ex_efidsT''_def: "ex_efidsT'' \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 2}
                else (if x = shopT then {Efid 121, Efid 9, Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_knosT :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosT_def: "ex_knosT \<equiv> (\<lambda> x :: identity. 
                  (if x = ''Eve'' then (\<lambda> l :: location. {} :: (identity * efid) set) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosT' :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosT'_def: "ex_knosT' \<equiv>(\<lambda> x :: identity. 
                  (if x = ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubT then 
                                  ({(''Alice'', Efid 2),(''Alice'', Efid 3),(''Alice'', Efid 11),
                                    (''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 11)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosT'' :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosT''_def: "ex_knosT'' \<equiv> (\<lambda> x :: identity.                       
                  (if x = ''Eve'' then 
                      (\<lambda> l :: location.
                          (if l = pubT then 
                                  ({(''Alice'', Efid 2),(''Alice'', Efid 3),(''Alice'', Efid 11),
                                    (''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 11)})
                            else (if l = shopT then 
                                     ({(''Eve'', Efid 121),(''Eve'', Efid 9),(''Eve'', Efid 5),(''Eve'', Efid 7),(''Eve'', Efid 13),
                                       (''Bob'', Efid 121),(''Bob'', Efid 9),(''Bob'', Efid 5),(''Bob'', Efid 7), (''Bob'', Efid 13), 
                                       (''Charly'', Efid 121),(''Charly'', Efid 9),(''Charly'', Efid 5),(''Charly'', Efid 7),(''Charly'', Efid 13),
                                       (''David'', Efid 121),(''David'', Efid 9),(''David'', Efid 5),(''David'', Efid 7), (''David'', Efid 13),
                                       (''Flo'', Efid 121),(''Flo'', Efid 9),(''Flo'', Efid 5),(''Flo'', Efid 7), (''Flo'', Efid 13)
                                      })
                                   else {})))
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

(* The nicer representation with case suffers from
   not so nice presentation in the cases (need to unfold the syntax)  
fixes ex_loc_ass_alt :: "location \<Rightarrow> identity set"
defines ex_loc_ass_alt_def: "ex_loc_ass_alt \<equiv>
          (\<lambda> x.  (case x of 
             Location (Suc 0) \<Rightarrow> {''Alice'', ''Bob'', ''Eve''}  
           | Location (Suc (Suc 0)) \<Rightarrow> {''Charly'', ''David''} 
           |  _ \<Rightarrow> {}))"
*)

(* Alternative attack that persists even in Level Two: 
   Bob gets isolated by Alice leaving pub so he's alone with Eve*)
fixes ex_credsTi :: "identity \<Rightarrow> efidlist"
defines ex_credsTi_def: 
          "ex_credsTi \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 1 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 0 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else 
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"

fixes ex_loc_assTi :: "location \<Rightarrow> identity set"
defines ex_loc_assTi_def: "ex_loc_assTi \<equiv>
          (\<lambda> x. if x = pubT then {''Bob'', ''Eve''}  
                 else (if x = shopT then {''Alice'', ''Charly'', ''David'', ''Flo''} 
                       else {}))"

fixes ex_efidsTi :: "location \<Rightarrow> efid set"
defines ex_efidsTi_def: "ex_efidsTi \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 3, Efid 11}
                else (if x = shopT then {Efid 4, Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_knosTi :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosTi_def: "ex_knosTi \<equiv>(\<lambda> x :: identity. 
                  (if x = ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubT then 
                                  ({(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 3),(''Eve'', Efid 11)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"


(* initial attack -- not working any more here after action refinement (see below) *)
fixes ex_graphT :: "igraph"
defines ex_graphT_def: "ex_graphT \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT ex_credsT ex_locsT ex_efidsT ex_knosT"

(* Eve gets the ex_knos *)
fixes ex_graphT' :: "igraph"
defines ex_graphT'_def: "ex_graphT' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT ex_credsT ex_locsT ex_efidsT ex_knosT'"

(* Bob goes to shop *)
fixes ex_graphT'' :: "igraph"
defines ex_graphT''_def: "ex_graphT'' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT' ex_credsT' ex_locsT ex_efidsT' ex_knosT'"

(* Eve goes to shop *)
fixes ex_graphT''' :: "igraph"
defines ex_graphT'''_def: "ex_graphT''' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT'' ex_credsT'' ex_locsT ex_efidsT'' ex_knosT'"

(* Eve gets ex_knos at shop *)
fixes ex_graphT'''' :: "igraph"
defines ex_graphT''''_def: "ex_graphT'''' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT'' ex_credsT'' ex_locsT ex_efidsT'' ex_knosT''"

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
fixes ex_graphTi :: "igraph"
defines ex_graphTi_def: "ex_graphTi \<equiv> Lgraph {(pubT, shopT)} ex_loc_assTi ex_credsTi ex_locsT ex_efidsTi ex_knosT"

(* Eve gets the ex_knos *)
fixes ex_graphTii :: "igraph"
defines ex_graphTii_def: "ex_graphTii \<equiv> Lgraph {(pubT, shopT)} ex_loc_assTi ex_credsTi ex_locsT ex_efidsTi ex_knosTi"

fixes local_policiesT :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesT_def: "local_policiesT G \<equiv> 
    (\<lambda> x. if x = pubT then  {(\<lambda> y. True, {get,move,put})}
          else (if x = shopT then {(\<lambda> y. True, {get,move,put})} 
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

fixes rmapT :: "InfrastructureTwo.infrastructure \<Rightarrow> InfrastructureOne.infrastructure"
defines rmapT_def:
"rmapT I \<equiv> InfrastructureTwo.ref_map I local_policiesO"

fixes corona_scenarioT :: "infrastructure"
defines corona_scenarioT_def:
"corona_scenarioT \<equiv> Infrastructure ex_graphT local_policiesT"
fixes IcoronaT :: "infrastructure set"
defines IcoronaT_def:
  "IcoronaT \<equiv> {corona_scenarioT}"

(* other states of scenario *)
(* First step: Bob goes to shop *)

fixes corona_scenarioT' :: "infrastructure"
defines corona_scenarioT'_def: "corona_scenarioT' \<equiv> Infrastructure ex_graphT' local_policiesT"
fixes CoronaT' :: "infrastructure set"
defines CoronaT'_def: "CoronaT' \<equiv> {corona_scenarioT'}"
fixes corona_scenarioT'' :: "infrastructure"
defines corona_scenarioT''_def: "corona_scenarioT'' \<equiv> Infrastructure ex_graphT'' local_policiesT"
fixes CoronaT'' :: "infrastructure set"
defines CoronaT''_def: "CoronaT'' \<equiv> {corona_scenarioT''}"
fixes corona_scenarioT''' :: "infrastructure"
defines corona_scenarioT'''_def: "corona_scenarioT''' \<equiv> Infrastructure ex_graphT''' local_policiesT"
fixes CoronaT''' :: "infrastructure set"
defines CoronaT'''_def: "CoronaT''' \<equiv> {corona_scenarioT'''}"
fixes corona_scenarioT'''' :: "infrastructure"
defines corona_scenarioT''''_def: "corona_scenarioT'''' \<equiv> Infrastructure ex_graphT'''' local_policiesT"
fixes CoronaT'''' :: "infrastructure set"
defines CoronaT''''_def: "CoronaT'''' \<equiv> {corona_scenarioT''''}"
(* Second attack where Alice leaves*)
fixes corona_scenarioTi :: "infrastructure"
defines corona_scenarioTi_def: "corona_scenarioTi \<equiv> Infrastructure ex_graphTi local_policiesT"
fixes CoronaTi :: "infrastructure set"
defines CoronaTi_def: "CoronaTi \<equiv> {corona_scenarioTi}"
fixes corona_scenarioTii :: "infrastructure"
defines corona_scenarioTii_def: "corona_scenarioTii \<equiv> Infrastructure ex_graphTii local_policiesT"
fixes CoronaTii :: "infrastructure set"
defines CoronaTii_def: "CoronaTii \<equiv> {corona_scenarioTii}"

fixes corona_statesT
defines corona_statesT_def: "corona_statesT \<equiv> { I. corona_scenarioT \<rightarrow>\<^sub>i* I }"
fixes corona_KripkeT
defines "corona_KripkeT \<equiv> Kripke corona_statesT IcoronaT"
fixes scoronaT 
defines "scoronaT \<equiv> {x. \<exists> n. \<not> global_policyT'' x (Efid n)}"  
fixes scoronaT' 
defines "scoronaT' \<equiv> {x. \<exists> n. \<not> global_policyT x (Efid n)}"  

begin
(* actor invariants for example *)
lemma all_actors: "actors_graph(graphI corona_scenarioT) = corona_actorsT"
proof (simp add: corona_scenarioT_def corona_actorsT_def ex_graphT_def actors_graph_def nodes_def
                 ex_loc_assT_def, rule equalityI)
  show "{x. \<exists>y. (y = shopT \<longrightarrow>
             (shopT = pubT \<longrightarrow> x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'') \<and>
             (shopT \<noteq> pubT \<longrightarrow> x = ''Charly'' \<or> x = ''David'' \<or> x = ''Flo'')) \<and>
            (y \<noteq> shopT \<longrightarrow>
             (y = pubT \<longrightarrow> (\<exists>y. y = shopT \<or> y = pubT \<and> pubT = shopT) \<and> (x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'')) \<and>
             y = pubT)}
    \<subseteq> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}"
    by auto
next show "{''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}
    \<subseteq> {x. \<exists>y. (y = shopT \<longrightarrow>
                (shopT = pubT \<longrightarrow> x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'') \<and>
                (shopT \<noteq> pubT \<longrightarrow> x = ''Charly'' \<or> x = ''David'' \<or> x = ''Flo'')) \<and>
               (y \<noteq> shopT \<longrightarrow>
                (y = pubT \<longrightarrow> (\<exists>y. y = shopT \<or> y = pubT \<and> pubT = shopT) \<and> (x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'')) \<and>
                y = pubT)}"
    using pubT_def shopT_def by auto
qed

lemma all_corona_actors: "(corona_scenarioT, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI y) = corona_actorsT"
  using all_actors same_actors by auto

(* nodes invariants *)
lemma same_nodes: "(corona_scenarioT, s) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> InfrastructureTwo.nodes (graphI corona_scenarioT) = InfrastructureTwo.nodes (graphI s)"
  using InfrastructureTwo.same_nodes by blast

(* efids invariants *)

lemma isthere_lem00: " a \<in>  agra (graphI corona_scenarioT) l \<Longrightarrow> l \<in> nodes (graphI corona_scenarioT) \<Longrightarrow>
            efids_cur (cgra (graphI corona_scenarioT) a) \<in> egra (graphI corona_scenarioT) l"
  apply (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def nodes_def ex_credsT_def ex_efidsT_def
             shopT_def pubT_def)
  by (smt (z3) One_nat_def Zero_not_Suc char.inject insertE list.inject location.inject shopT_def singleton_iff)


lemma efids_root_lem: "a \<in> actors_graph (InfrastructureTwo.graphI corona_scenarioT) \<Longrightarrow> 
                      a' \<in> actors_graph (InfrastructureTwo.graphI corona_scenarioT) \<Longrightarrow>
                 a \<noteq> a' \<Longrightarrow>
                  efids_root (cgra (InfrastructureTwo.graphI corona_scenarioT) a) \<noteq> 
                  efids_root (cgra (InfrastructureTwo.graphI corona_scenarioT) a')"
    apply (simp add: rmapT_def ref_map_def move_graph_a_def  corona_scenarioT_def Infrastructure.move_graph_a_def)
  apply (simp add: repl_efr_def ex_graphT_def ex_credsT_def)
  by (smt CollectD InfrastructureTwo.actors_graph_def InfrastructureTwo.agra.simps InfrastructureTwo.gra.simps InfrastructureTwo.nodes_def ex_loc_assT_def insertE prod.inject singletonD)


lemma efids_root_minus: "(corona_scenarioT, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
      \<Longrightarrow> a \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI I) l 
      \<Longrightarrow> l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI I)  \<Longrightarrow>
(\<lambda>x. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) x)) `
       (InfrastructureTwo.agra (InfrastructureTwo.graphI I) l - {a}) =
       (\<lambda>a. efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)) `
       InfrastructureTwo.agra (InfrastructureTwo.graphI I) l -
       {efids_root (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)}"
  apply auto
  apply (frule InfrastructureTwo.eroots_inj_on_inv)
  using efids_root_lem inj_on_def apply blast
  by (metis (mono_tags, lifting) InfrastructureTwo.actors_graph_def inj_on_def mem_Collect_eq)


text \<open>Other invariants are that the efids at egra l are in fact efids of the actors at
      that location, i.e. 
       e \<in> egra G l = (\<exists>! a \<in> agra G l.  e \<in> efid_list (cgra G a) (for InfrastructureTwo))
                      .....        /\ e = efid_root (cgra G a) 
            \<close>
lemma range_disjoint_corona_scenarioO[rule_format]: "(\<forall> a \<in> actors_graph (InfrastructureTwo.graphI corona_scenarioT). 
   (\<forall> a' \<in> actors_graph(InfrastructureTwo.graphI corona_scenarioT). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) a)) \<inter> 
      (range (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) a')))) = {})))"
proof (unfold corona_scenarioT_def ex_graphT_def ex_credsT_def, simp)
  show " \<forall>a\<in>InfrastructureTwo.actors_graph
         (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
           (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                     else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                          else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                               else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                    else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                         else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
           ex_locsT ex_efidsT ex_knosT).
       (a = ''Flo'' \<longrightarrow>
        (\<forall>a'\<in>InfrastructureTwo.actors_graph
               (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                 (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                      else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                           else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                     else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                          else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                               else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                 ex_locsT ex_efidsT ex_knosT).
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
         (\<forall>a'\<in>InfrastructureTwo.actors_graph
                (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                  (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                       else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                            else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                 else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                      else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                           else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                  ex_locsT ex_efidsT ex_knosT).
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
          (\<forall>a'\<in>InfrastructureTwo.actors_graph
                 (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                   (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                        else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                             else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                  else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                       else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                            else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                 else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                   ex_locsT ex_efidsT ex_knosT).
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
           (\<forall>a'\<in>InfrastructureTwo.actors_graph
                  (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                    (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                         else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                              else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                   else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                        else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                             else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                  else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                    ex_locsT ex_efidsT ex_knosT).
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
            (\<forall>a'\<in>InfrastructureTwo.actors_graph
                   (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                     (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                          else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                               else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                    else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                         else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                              else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                   else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                     ex_locsT ex_efidsT ex_knosT).
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
             (\<forall>a'\<in>InfrastructureTwo.actors_graph
                    (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                      (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                           else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                                else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                     else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                          else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                               else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                    else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                      ex_locsT ex_efidsT ex_knosT).
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
             (\<forall>a'\<in>InfrastructureTwo.actors_graph
                    (InfrastructureTwo.igraph.Lgraph {(pubT, shopT)} ex_loc_assT
                      (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                           else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                                else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                     else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                          else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                               else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                    else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                      ex_locsT ex_efidsT ex_knosT).
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
    by (smt (z3) InfrastructureTwo.actors_graph_def InfrastructureTwo.agra.simps all_not_in_conv ex_loc_assT_def insertE mem_Collect_eq)
qed


lemma inj_on_corona_scenarioT: "inj_on (\<lambda>x. efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) x))
        (InfrastructureTwo.actors_graph (InfrastructureTwo.graphI corona_scenarioT))"
  by (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def nodes_def
                    ex_credsT_def ex_locsT_def ex_efidsT_def ex_knosT_def inj_on_def
                    actors_graph_def)

lemma l_eq_corona_scenarioT[rule_format]: "(\<forall> l l'. l \<in> nodes (graphI corona_scenarioT) \<longrightarrow>
                a \<in>  agra (graphI corona_scenarioT) l \<longrightarrow>  a \<in>  agra (graphI corona_scenarioT) l' \<longrightarrow> l = l')"
  by (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def nodes_def)

lemma coronaT_efids_list_inj: 
"a \<in> actors_graph(InfrastructureTwo.graphI corona_scenarioT) \<Longrightarrow> 
inj (efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) a))"
  by (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def nodes_def
                    ex_credsT_def ex_locsT_def ex_efidsT_def ex_knosT_def pubT_def shopT_def inj_def)
  
lemma efid_in_range_corona_scenarioT: "(\<forall> l \<in> nodes (graphI corona_scenarioT).
         (\<forall> e \<in> (egra (InfrastructureTwo.graphI corona_scenarioT) l).
         (\<exists> a \<in> actors_graph (graphI corona_scenarioT). 
             e \<in> range (efids_list (InfrastructureTwo.cgra (graphI corona_scenarioT) a)))))"
  apply (simp add: corona_scenarioT_def ex_graphT_def nodes_def)
  apply (rule allI)
   apply (rule impI)+
   apply (rule ballI)
  apply (simp add: ex_efidsT_def actors_graph_def ex_loc_assT_def)
  apply (erule exE)
  apply (erule disjE)
   apply (simp add: pubT_def shopT_def ex_credsT_def nodes_def)
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
   apply (simp add: pubT_def shopT_def ex_credsT_def nodes_def)
   apply (erule disjE)
   apply (rule_tac x = "''Charly''" in exI)
  apply simp
   apply (erule disjE)
   apply (rule_tac x = "''David''" in exI)
  apply simp
  apply (rule_tac x = "''Flo''" in exI)
  by simp

lemma efid_kgra_in_range_corona_scenarioT: "(\<forall> l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT). 
         (\<forall> h \<in> InfrastructureTwo.actors_graph(InfrastructureTwo.graphI corona_scenarioT).
         (\<forall> e \<in> (snd`((InfrastructureTwo.kgra (InfrastructureTwo.graphI corona_scenarioT) h l))).
         (\<exists> a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI corona_scenarioT). 
           e \<in> range (InfrastructureTwo.efids_list (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) a))))))"
  by (simp add: corona_scenarioT_def ex_graphT_def nodes_def
                 ex_credsT_def ex_locsT_def ex_efidsT_def ex_knosT_def pubT_def shopT_def)

lemma efid_eq_efid_cur_corona_scenarioT: "lb \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI corona_scenarioT) lb \<Longrightarrow>
       \<exists>a\<in>InfrastructureTwo.agra (InfrastructureTwo.graphI corona_scenarioT) lb.
          e = efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) a)"
  apply (simp add: corona_scenarioT_def ex_graphT_def nodes_def ex_loc_assT_def 
                 ex_credsT_def ex_locsT_def ex_efidsT_def ex_knosT_def pubT_def shopT_def)
  using shopT_def by fastforce

lemma anonymous_actor_corona_scenarioT: " lb \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) \<Longrightarrow>
       e \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI corona_scenarioT) lb \<Longrightarrow>
       anonymous_actor corona_scenarioT e \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI corona_scenarioT) lb"
  apply (subgoal_tac "InfrastructureTwo.actors_graph (InfrastructureTwo.graphI corona_scenarioT) \<noteq> {}")
  apply (drule anonymous_actor_defO)
  using coronaT_efids_list_inj apply blast
      apply (simp add: range_disjoint_corona_scenarioO, assumption)
  apply (simp add: corona_scenarioT_def ex_graphT_def nodes_def ex_loc_assT_def local_policiesT_def
                 ex_credsT_def ex_locsT_def ex_efidsT_def ex_knosT_def pubT_def shopT_def)
    apply (erule exE)
    apply (erule disjE)
     apply (simp add: actors_graph_def)  
  oops


lemma refmap_lem_egra_unique_corona_scenarioT: 
"(\<forall> a \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI corona_scenarioT). 
     (\<forall> l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT). 
       (\<forall> l' \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT). 
        ((a @\<^bsub>(InfrastructureTwo.graphI corona_scenarioT)\<^esub> l) \<longrightarrow>
        (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioT) a)
       \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI corona_scenarioT) l') 
       \<longrightarrow> l = l' ))))"
  by (metis (mono_tags, lifting) efid_eq_efid_cur_corona_scenarioT inj_on_cong inj_on_corona_scenarioT l_eq_corona_scenarioT refmap_lem_egra_unique_prepO)

lemma rtrancl_imp_step: "(I \<rightarrow>\<^sub>n y) \<Longrightarrow>  (I, y) \<in> {(x::InfrastructureOne.infrastructure, y::InfrastructureOne.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* "
  by (simp add: r_into_rtrancl) 
  
lemma rtrancl_imp_two_step: "(I \<rightarrow>\<^sub>n y) \<Longrightarrow>  (y \<rightarrow>\<^sub>n z) \<Longrightarrow> (I, z) \<in> {(x::InfrastructureOne.infrastructure, y::InfrastructureOne.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* "
  by (simp add: converse_rtrancl_into_rtrancl)

(* We need an invariant on put-enabledness that can only be proved at the level of the concrete example CoronaApp
   since in local_policies the infrastructure graph is a parameter to the local_policies component. *) 
lemma put_enables_initial: 
"(\<forall> a \<in> actors_graph (graphI corona_scenarioT). \<forall> l \<in> nodes (graphI corona_scenarioT). 
enables corona_scenarioT l (Actor a) put)"
  by (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def nodes_def local_policiesT_def
          ex_credsT_def pubT_def shopT_def ex_locsT_def ex_efidsT_def enables_def InfrastructureTwo.actors_graph_def)

lemma put_enables_init_reach: 
"(corona_scenarioT, y) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
(\<forall> l \<in> nodes (graphI corona_scenarioT).
       \<forall> xa \<in> InfrastructureTwo.delta corona_scenarioT (InfrastructureTwo.graphI corona_scenarioT) l. 
            xa \<in> InfrastructureTwo.delta y (InfrastructureTwo.graphI y) l)"
proof (erule rtrancl_induct)
  show " \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT).
       \<forall>xa\<in>InfrastructureTwo.delta corona_scenarioT (InfrastructureTwo.graphI corona_scenarioT) l.
          xa \<in> InfrastructureTwo.delta corona_scenarioT (InfrastructureTwo.graphI corona_scenarioT) l"
    by simp
next show "\<And>y z. (corona_scenarioT, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT).
              \<forall>xa\<in>InfrastructureTwo.delta corona_scenarioT (InfrastructureTwo.graphI corona_scenarioT) l.
                 xa \<in> InfrastructureTwo.delta y (InfrastructureTwo.graphI y) l \<Longrightarrow>
           \<forall>l\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT).
              \<forall>xa\<in>InfrastructureTwo.delta corona_scenarioT (InfrastructureTwo.graphI corona_scenarioT) l.
                 xa \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l "
  apply (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def nodes_def local_policiesT_def
          ex_credsT_def pubT_def shopT_def ex_locsT_def ex_efidsT_def enables_def InfrastructureTwo.actors_graph_def)
    apply (rule allI)
    apply (drule_tac x = l in spec)
    by (metis (no_types, lifting) InfrastructureTwo.delta.simps InfrastructureTwo.delta_invariant InfrastructureTwo.init_state_policy0 local_policiesT_def numeral_1_eq_Suc_0 numerals(1) shopT_def singleton_iff)
qed

(* not possible to prove

lemma delta_pres_step: "(\<forall>z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow>  (\<forall> l \<in> nodes (graphI z).
       \<forall> xa \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l. 
            xa \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l))"
proof (clarify, frule delta_invariant, erule state_transition_in.cases)
  show "\<And>z z' l a b G I aa la I'.
       l \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI z) \<Longrightarrow>
       (a, b) \<in> InfrastructureTwo.delta z (InfrastructureTwo.graphI z) l \<Longrightarrow>
       InfrastructureTwo.delta z = InfrastructureTwo.delta z' \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       InfrastructureTwo.enables I la (Actor aa) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (aa := (InfrastructureTwo.kgra G aa)
              (la := {(x, y). x \<in> InfrastructureTwo.agra G la \<and> y \<in> InfrastructureTwo.egra G la}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       (a, b) \<in> InfrastructureTwo.delta z' (InfrastructureTwo.graphI z') l"
    oops
*)

lemma put_enables_pres_refl[rule_format]: 
"(corona_scenarioT, s) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> (\<forall> a \<in> actors_graph (graphI s). \<forall> l \<in> nodes (graphI s). enables s l (Actor a) put)"
  apply (rule put_enables_invariant_refOO, assumption)
  using put_enables_init_reach apply blast
  using put_enables_initial by blast


lemma refmapTwo_lem: "\<forall>s::InfrastructureTwo.infrastructure.
       (corona_scenarioT, s) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
        (\<forall>s'. s \<rightarrow>\<^sub>n s' \<longrightarrow> (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*)"
proof (clarify, frule same_nodes, frule init_state_policy, erule state_transition_in.cases)
(* move case *)
  show "\<And>s s' G I a l l' I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (case_tac "l = l'")
    show "\<And>s s' G I a l l' I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l = l' \<Longrightarrow> (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
      using InfrastructureTwo.move_graph_eq InfrastructureTwo.ref_map_def rmapT_def by force
  next show "\<And>s s' G I a l l' I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow> (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (rule_tac y = "InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI (rmapT s)))
        (InfrastructureOne.delta (rmapT s))" in rtrancl_imp_two_step)
    show "\<And>s s' G I a l l' I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       rmapT
        s \<rightarrow>\<^sub>n InfrastructureOne.infrastructure.Infrastructure
                (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI (rmapT s)))
                (InfrastructureOne.delta (rmapT s))"
  apply (rule_tac I = "rmapT s" and I' = "(InfrastructureOne.infrastructure.Infrastructure
                (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI (rmapT s)))
                (InfrastructureOne.delta (rmapT s)))" and l = l and l' = l' 
                             and a = a 
 in InfrastructureOne.state_transition_in.move)
  apply (rule refl)
         apply (simp add: rmapT_def ref_map_def atI_def InfrastructureOne.atI_def)
         apply (simp add: rmapT_def ref_map_def nodes_def InfrastructureOne.nodes_def)
         apply (simp add: rmapT_def ref_map_def nodes_def InfrastructureOne.nodes_def)
      apply (simp add: rmapT_def ref_map_def actors_graph_def InfrastructureOne.actors_graph_def)
    apply (simp add: Infrastructure.nodes_def InfrastructureOne.nodes_def)
      apply (simp add: nodes_def Infrastructure.nodes_def atI_def rmapT_def local_policiesO_def)
(* *)
     apply (simp add: rmapT_def ref_map_def enables_def InfrastructureOne.enables_def local_policiesO_def shop_def pubO_def)
      apply (metis InfrastructureTwo.delta.simps corona_scenarioT_def empty_iff local_policiesT_def pubT_def shopO_def shopT_def)
    by (rule refl)
next show "\<And>s s' G I a l l' I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureTwo.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.move_graph_a a l l' (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI (rmapT s)))
        (InfrastructureOne.delta (rmapT s)) \<rightarrow>\<^sub>n rmapT s'"
  apply (rule_tac I = "InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI (rmapT s)))
        (InfrastructureOne.delta (rmapT s))" and I' = "rmapT s'" and l = l'
                             and a = a 
 in InfrastructureOne.state_transition_in.put)
apply (rule refl)
         apply (simp add: rmapT_def ref_map_def atI_def InfrastructureOne.atI_def)
         apply (simp add: rmapT_def ref_map_def nodes_def InfrastructureOne.nodes_def)
      apply (simp add: rmapT_def ref_map_def actors_graph_def InfrastructureOne.actors_graph_def)
      apply (simp add: InfrastructureOne.move_graph_a_def)
     apply (simp add: rmapT_def ref_map_def enables_def InfrastructureOne.enables_def local_policiesO_def shop_def pubO_def)
      apply (metis InfrastructureTwo.delta.simps corona_scenarioT_def empty_iff local_policiesT_def pubT_def shopO_def shopT_def)

(* need invariant for that *)
    apply (subgoal_tac "InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<notin>
                         (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')")
(* This should follow from invariant and l \<noteq> l'*)
    apply (subgoal_tac "\<not>(a  @\<^bsub>G\<^esub> l')") 
apply (simp add: rmapT_def ref_map_def move_graph_a_def InfrastructureOne.move_graph_a_def )
    apply clarify
     apply (rule conjI)
    prefer 2
    using InfrastructureTwo.atI_def apply blast
      apply (rule impI)+    
    apply (simp add: InfrastructureOne.put_graph_efid_def InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)
    using InfrastructureTwo.actor_unique_loc_lem InfrastructureTwo.atI_def l_eq_corona_scenarioT apply blast
(* here: still need to show invariant :
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)
       \<notin> InfrastructureTwo.egra (InfrastructureTwo.graphI I) l' 
equivalent to:
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       l' \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       a \<in> InfrastructureTwo.actors_graph G \<Longrightarrow>
       InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)
       \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI I) l' 
\<Longrightarrow> l = l'

*)
    apply (erule contrapos_nn)
    apply (erule_tac refmap_lem_egra_unique_refl)
    using efid_eq_efid_cur_corona_scenarioT apply blast
    using l_eq_corona_scenarioT apply force
    using range_disjoint_corona_scenarioO apply presburger
    using InfrastructureTwo.efids_list_inj_imp_inc_ind_not_eq coronaT_efids_list_inj apply presburger
    using inj_on_corona_scenarioT apply blast
    apply simp
       apply simp
      apply simp
     apply simp
by (simp add: InfrastructureOne.efids_cur_def InfrastructureTwo.efids_cur_def)
qed
(* previous attempt stepwise that lead on to understand the invariant:
     apply (unfold InfrastructureOne.put_graph_efid_def )
     apply (subgoal_tac 
     "((InfrastructureOne.egra
           (InfrastructureOne.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI I))
             ((InfrastructureTwo.agra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.agra (InfrastructureTwo.graphI I) l - {a},
               l' := insert a (InfrastructureTwo.agra (InfrastructureTwo.graphI I) l')))
             (InfrastructureTwo.cgra (InfrastructureTwo.graphI I)) (InfrastructureTwo.lgra (InfrastructureTwo.graphI I))
             ((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                    {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
               l' :=
                 insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
             (InfrastructureTwo.kgra (InfrastructureTwo.graphI I))))
         (l' :=
            insert
             (InfrastructureOne.efids_cur
               (InfrastructureOne.efids_inc_ind
                 (InfrastructureOne.cgra
                   (InfrastructureOne.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI I))
                     ((InfrastructureTwo.agra (InfrastructureTwo.graphI I))
                      (l := InfrastructureTwo.agra (InfrastructureTwo.graphI I) l - {a},
                       l' := insert a (InfrastructureTwo.agra (InfrastructureTwo.graphI I) l')))
                     (InfrastructureTwo.cgra (InfrastructureTwo.graphI I))
                     (InfrastructureTwo.lgra (InfrastructureTwo.graphI I))
                     ((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
                      (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                            {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
                       l' :=
                         insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                          (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
                     (InfrastructureTwo.kgra (InfrastructureTwo.graphI I)))
                   a)))
             (InfrastructureOne.egra
               (InfrastructureOne.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI I))
                 ((InfrastructureTwo.agra (InfrastructureTwo.graphI I))
                  (l := InfrastructureTwo.agra (InfrastructureTwo.graphI I) l - {a},
                   l' := insert a (InfrastructureTwo.agra (InfrastructureTwo.graphI I) l')))
                 (InfrastructureTwo.cgra (InfrastructureTwo.graphI I))
                 (InfrastructureTwo.lgra (InfrastructureTwo.graphI I))
                 ((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
                  (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                        {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
                   l' :=
                     insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                      (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
                 (InfrastructureTwo.kgra (InfrastructureTwo.graphI I)))
               l' -
              {InfrastructureOne.efids_cur
                (InfrastructureOne.cgra
                  (InfrastructureOne.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI I))
                    ((InfrastructureTwo.agra (InfrastructureTwo.graphI I))
                     (l := InfrastructureTwo.agra (InfrastructureTwo.graphI I) l - {a},
                      l' := insert a (InfrastructureTwo.agra (InfrastructureTwo.graphI I) l')))
                    (InfrastructureTwo.cgra (InfrastructureTwo.graphI I))
                    (InfrastructureTwo.lgra (InfrastructureTwo.graphI I))
                    ((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
                     (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                           {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
                      l' :=
                        insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                         (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
                    (InfrastructureTwo.kgra (InfrastructureTwo.graphI I)))
                  a)}))) = 
(((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                    {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
               l' :=
                 insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
         (l' :=
            insert (InfrastructureOne.efids_cur (InfrastructureOne.efids_inc_ind
                                                     (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
             ( ((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
                  (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                        {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
                   l' :=
                     insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                      (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
                 l' -
              {InfrastructureOne.efids_cur
                (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)}))) ")
(* test *)
      prefer 2
      apply simp
    apply (subgoal_tac "(((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                    {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
               l' :=
                 insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
         (l' :=
            insert (InfrastructureOne.efids_cur (InfrastructureOne.efids_inc_ind
                                                     (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
             ( ((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
                  (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                        {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
                   l' :=
                     insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                      (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
                 l' -
              {InfrastructureOne.efids_cur
                (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)}))) =
(((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                    {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
               l' :=
                 insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
         (l' :=
            insert (InfrastructureOne.efids_cur (InfrastructureOne.efids_inc_ind
                                                     (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
             ((insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                      (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')
              ) -
              {InfrastructureOne.efids_cur
                (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)})))")
      prefer 2
      apply simp
(* step 3 *)
    apply (subgoal_tac "(((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                    {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
               l' :=
                 insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
         (l' :=
            insert (InfrastructureOne.efids_cur (InfrastructureOne.efids_inc_ind
                                                     (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
             ((insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                      (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')
              ) -
              {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)}))) =
(((InfrastructureTwo.egra (InfrastructureTwo.graphI I))
              (l := InfrastructureTwo.egra (InfrastructureTwo.graphI I) l -
                    {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)},
               l' :=
                 insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')))
         (l' :=
            insert (InfrastructureOne.efids_cur (InfrastructureOne.efids_inc_ind
                                                     (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)))
              (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')
              ))")
      prefer 2
    apply (subgoal_tac " ((insert (InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a))
                      (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')
              ) -
              {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)}) =
             (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')")
       prefer 2
    apply (subgoal_tac "InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a) \<notin>
                         (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')")
        apply simp
    defer
       apply simp
    apply simp
    apply (rule conjI)
     apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)
     apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)

     apply (rule impI)+
     apply (rule conjI)
      apply blast
    apply (subgoal_tac "l = l'")
    apply simp
     apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)
    apply (simp add: nodes_def Infrastructure.nodes_def atI_def rmapT_def local_policiesO_def ref_map_def put_graph_efid_def
                  InfrastructureOne.put_graph_efid_def move_graph_a_def InfrastructureOne.move_graph_a_def)

    apply (rule conjI)
     apply (rule impI)
     apply (rule conjI)
     apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)

    apply (subgoal_tac "InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)
        \<notin>  (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')")
    apply (subgoal_tac "(InfrastructureTwo.egra (InfrastructureTwo.graphI I) l' -
             {InfrastructureOne.efids_cur (InfrastructureTwo.cgra (InfrastructureTwo.graphI I) a)}) =
              (InfrastructureTwo.egra (InfrastructureTwo.graphI I) l')")
      apply (rotate_tac -1)
    apply (erule ssubst)
      apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)
    apply simp

     apply (simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def
                      InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def)
     prefer 2
     apply (rule impI)
    apply (rule conjI)

    apply simp
    prefer 2
*)
(* get case *)
qed
next show "\<And>s s' G I a l I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (a := (InfrastructureTwo.kgra G a)
              (l := {(x, y). x \<in> InfrastructureTwo.agra G l \<and> y \<in> InfrastructureTwo.egra G l}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (rule rtrancl_imp_step, rule_tac I =  "rmapT s" and I' = "rmapT s'" and l = l  and a = a  
        in InfrastructureOne.state_transition_in.get, 
        rule refl, simp add: rmapT_def ref_map_def atI_def InfrastructureOne.atI_def
        local_policiesO_def InfrastructureOne.nodes_def shopO_def pubO_def)
    show "\<And>s s' G I a l I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureTwo.nodes G \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (a := (InfrastructureTwo.kgra G a)
              (l := {(x, y). x \<in> InfrastructureTwo.agra G l \<and> y \<in> InfrastructureTwo.egra G l}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI (rmapT s))"
      apply (simp add: rmapT_def local_policiesO_def ref_map_def)
      using InfrastructureOne.nodes_def InfrastructureTwo.nodes_def by fastforce
  next show "\<And>s s' G I a l I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (a := (InfrastructureTwo.kgra G a)
              (l := {(x, y). x \<in> InfrastructureTwo.agra G l \<and> y \<in> InfrastructureTwo.egra G l}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       InfrastructureOne.enables (rmapT s) l (Actor a) get"
   proof (simp add: rmapT_def ref_map_def nodes_def enables_def InfrastructureOne.enables_def
              local_policiesO_def InfrastructureOne.nodes_def shopO_def pubO_def)
     show "\<And>s s' G I a l I'.
       (corona_scenarioT, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       {x. \<exists>y. (x, y) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI corona_scenarioT) \<or>
               (y, x) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI corona_scenarioT)} =
       {x. \<exists>y. (x, y) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI I) \<or>
               (y, x) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI I)} \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta I \<Longrightarrow>
       s = I \<Longrightarrow>
       s' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI I))
          (InfrastructureTwo.agra (InfrastructureTwo.graphI I)) (InfrastructureTwo.cgra (InfrastructureTwo.graphI I))
          (InfrastructureTwo.lgra (InfrastructureTwo.graphI I)) (InfrastructureTwo.egra (InfrastructureTwo.graphI I))
          ((InfrastructureTwo.kgra (InfrastructureTwo.graphI I))
           (a := (InfrastructureTwo.kgra (InfrastructureTwo.graphI I) a)
              (l := InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<times>
                    InfrastructureTwo.egra (InfrastructureTwo.graphI I) l))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureTwo.graphI I\<^esub> l \<Longrightarrow>
       \<exists>x\<in>InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l. case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI I))
          (InfrastructureTwo.agra (InfrastructureTwo.graphI I)) (InfrastructureTwo.cgra (InfrastructureTwo.graphI I))
          (InfrastructureTwo.lgra (InfrastructureTwo.graphI I)) (InfrastructureTwo.egra (InfrastructureTwo.graphI I))
          ((InfrastructureTwo.kgra (InfrastructureTwo.graphI I))
           (a := (InfrastructureTwo.kgra (InfrastructureTwo.graphI I) a)
              (l := InfrastructureTwo.agra (InfrastructureTwo.graphI I) l \<times>
                    InfrastructureTwo.egra (InfrastructureTwo.graphI I) l))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l \<noteq> Location (Suc 0) \<longrightarrow> l = Location 0"
        by (metis InfrastructureTwo.delta.simps One_nat_def corona_scenarioT_def empty_iff local_policiesT_def pubT_def shopT_def)
    qed
 next show "\<And>s s' G I a l I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure
        (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra G) (InfrastructureTwo.agra G) (InfrastructureTwo.cgra G)
          (InfrastructureTwo.lgra G) (InfrastructureTwo.egra G)
          ((InfrastructureTwo.kgra G)
           (a := (InfrastructureTwo.kgra G a)
              (l := {(x, y). x \<in> InfrastructureTwo.agra G l \<and> y \<in> InfrastructureTwo.egra G l}))))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       rmapT s' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI (rmapT s)))
          (InfrastructureOne.agra (InfrastructureOne.graphI (rmapT s)))
          (InfrastructureOne.cgra (InfrastructureOne.graphI (rmapT s)))
          (InfrastructureOne.lgra (InfrastructureOne.graphI (rmapT s)))
          (InfrastructureOne.egra (InfrastructureOne.graphI (rmapT s)))
          ((InfrastructureOne.kgra (InfrastructureOne.graphI (rmapT s)))
           (a := (InfrastructureOne.kgra (InfrastructureOne.graphI (rmapT s)) a)
              (l := {(x, y).
                     x \<in> InfrastructureOne.agra (InfrastructureOne.graphI (rmapT s)) l \<and>
                     y \<in> InfrastructureOne.egra (InfrastructureOne.graphI (rmapT s)) l}))))
        (InfrastructureOne.delta (rmapT s))"
by (simp add: rmapT_def ref_map_def)
  qed
next show "\<And>s s' G I a l I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a l G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  proof (rule rtrancl_imp_step, rule_tac I = "rmapT s" and I' = "rmapT s'" and l = l  
                             and a = a 
 in InfrastructureOne.state_transition_in.put, rule refl, simp add: rmapT_def ref_map_def atI_def InfrastructureOne.atI_def
     ,simp add: rmapT_def ref_map_def nodes_def enables_def InfrastructureOne.enables_def
              local_policiesO_def InfrastructureOne.nodes_def shopO_def pubO_def)
    show "\<And>s s' G I a l I'.
       (corona_scenarioT, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       {x. \<exists>y. (x, y) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI corona_scenarioT) \<or>
               (y, x) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI corona_scenarioT)} =
       {x. \<exists>y. (x, y) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI I) \<or>
               (y, x) \<in> InfrastructureTwo.gra (InfrastructureTwo.graphI I)} \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta I \<Longrightarrow>
       s = I \<Longrightarrow>
       s' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a l (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureTwo.graphI I\<^esub> l \<Longrightarrow>
       \<exists>x\<in>InfrastructureTwo.delta I (InfrastructureTwo.graphI I) l. case x of (p, e) \<Rightarrow> put \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a l (InfrastructureTwo.graphI I))
        (InfrastructureTwo.delta I) \<Longrightarrow>
       l \<noteq> Location (Suc 0) \<longrightarrow> l = Location 0"
      using all_not_in_conv corona_scenarioT_def local_policiesT_def pubT_def shopT_def by fastforce
  next show "\<And>s s' G I a l I'.
       (corona_scenarioT, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT) =
       InfrastructureTwo.nodes (InfrastructureTwo.graphI s) \<Longrightarrow>
       InfrastructureTwo.delta corona_scenarioT = InfrastructureTwo.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureTwo.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureTwo.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureTwo.infrastructure.Infrastructure (InfrastructureTwo.put_graph_efid a l G)
        (InfrastructureTwo.delta I) \<Longrightarrow>
       rmapT s' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.put_graph_efid a l (InfrastructureOne.graphI (rmapT s))) (InfrastructureOne.delta (rmapT s))"
      apply (simp add: rmapT_def ref_map_def)
    apply (simp add: put_graph_efid_def InfrastructureOne.put_graph_efid_def)
      apply (rule conjI)
       apply (rule ext, simp add: InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def)
       apply (rule ext, simp)
      apply (rule impI)
      by (simp add: InfrastructureTwo.efids_cur_def InfrastructureOne.efids_cur_def
                       InfrastructureTwo.efids_inc_ind_def InfrastructureOne.efids_inc_ind_def)
qed
qed

theorem refmapTwo: "corona_KripkeO \<sqsubseteq>\<^sub>rmapT corona_KripkeT"
proof (rule strong_mt'', simp add: corona_KripkeT_def corona_KripkeO_def corona_statesT_def corona_statesO_def state_transition_refl_def, rule conjI)
  show "IcoronaT \<subseteq> {I. (corona_scenarioT, I) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*}"
    using IcoronaT_def by fastforce
next show "IcoronaO \<subseteq> {I. (corona_scenarioO, I) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*} \<and>
    rmapT ` IcoronaT \<subseteq> IcoronaO \<and>
    (\<forall>s. (\<exists>s0\<in>IcoronaT. (s0, s) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*) \<longrightarrow>
         (\<forall>s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (rmapT s, rmapT s') \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*))"
    apply (rule conjI)
    using IcoronaO_def apply blast
    apply (rule conjI)
     apply (simp add: rmapT_def ref_map_def IcoronaO_def IcoronaT_def corona_scenarioO_def corona_scenarioT_def
                      ex_graphO_def ex_graphT_def pubO_def pubT_def  ex_loc_assT_def
            ex_loc_assO_def ext ex_credsO_def  ex_credsT_def ex_locsO_def ex_locsT_def 
            ex_efidsT_def ex_efidsO_def shopO_def shopT_def
            ex_knosT_def ex_knosO_def repl_efr_def)
    using IcoronaT_def InfrastructureOne.state_transition_infra_def InfrastructureTwo.state_transition_infra_def refmapTwo_lem by auto
  (*  using IcoronaT_def InfrastructureTwo.state_transition_infra_def refmapTwo_lem by auto *)
qed

(* The steps from the previous attack of level 1 still work still (but won't allow identification) *)
lemma step1: "corona_scenarioT  \<rightarrow>\<^sub>n corona_scenarioT'"
proof (rule_tac l = pubT and a = "''Eve''" in get)
  show "graphI corona_scenarioT = graphI corona_scenarioT" by (rule refl)
next show "''Eve'' @\<^bsub>graphI corona_scenarioT\<^esub> pubT" 
    by (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def atI_def nodes_def)
next show "enables corona_scenarioT pubT (Actor ''Eve'') get"
    by (simp add: enables_def corona_scenarioT_def ex_graphT_def local_policiesT_def
                    ex_credsT_def ex_locsT_def)
next show "pubT \<in> nodes (graphI corona_scenarioT)"
    using corona_scenarioT_def ex_graphT_def nodes_def by auto 
next show "corona_scenarioT' =
    Infrastructure
     (Lgraph (gra (graphI corona_scenarioT)) (agra (graphI corona_scenarioT)) (cgra (graphI corona_scenarioT))
       (lgra (graphI corona_scenarioT)) (egra (graphI corona_scenarioT))
       ((kgra (graphI corona_scenarioT))
        (''Eve'' := (kgra (graphI corona_scenarioT) (''Eve''))
           (pubT := {(x, y). x \<in> agra (graphI corona_scenarioT) pubT \<and> y \<in> egra (graphI corona_scenarioT) pubT}))))
     (delta corona_scenarioT)"
    apply (simp add: corona_scenarioT'_def ex_graphT'_def move_graph_a_def 
                     corona_scenarioT_def ex_graphT_def pubT_def shopT_def 
                     ex_loc_assT'_def ex_loc_assT_def ex_efidsT'_def ex_efidsT_def 
                     ex_knosT_def ex_knosT'_def ex_credsT_def)
    apply (rule ext, simp add: insert_Diff_if shopT_def pubT_def)
      apply (rule impI, rule ext)
by auto[1]
qed

lemma step1r: "corona_scenarioT  \<rightarrow>\<^sub>n* corona_scenarioT'"
proof (simp add: state_transition_in_refl_def)
  show " (corona_scenarioT, corona_scenarioT') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "corona_scenarioT'  \<rightarrow>\<^sub>n corona_scenarioT''"
proof (rule_tac l' = shopT and l = pubT and a = "''Bob''" in move, rule refl)
  show "''Bob'' @\<^bsub>graphI corona_scenarioT'\<^esub> pubT"
   by (simp add: corona_scenarioT'_def ex_graphT'_def pubT_def shopT_def atI_def ex_loc_assT_def)
next show "pubT \<in> nodes (graphI corona_scenarioT')"
    by (simp add: corona_scenarioT'_def ex_graphT'_def pubT_def atI_def nodes_def, blast)
next show "shopT \<in> nodes (graphI corona_scenarioT')"
    by (simp add: corona_scenarioT'_def nodes_def ex_graphT'_def, blast)
next show "''Bob'' \<in> actors_graph (graphI corona_scenarioT')"
    by (simp add: actors_graph_def corona_scenarioT'_def ex_graphT'_def nodes_def
                     ex_loc_assT_def shopT_def pubT_def, blast)
next show "enables corona_scenarioT' shopT (Actor ''Bob'') move"
    by (simp add: enables_def corona_scenarioT'_def local_policiesT_def)
next show "corona_scenarioT'' =
    Infrastructure (move_graph_a ''Bob'' pubT shopT (graphI corona_scenarioT')) (delta corona_scenarioT')"
    apply (simp add: corona_scenarioT'_def ex_graphT''_def move_graph_a_def corona_scenarioT''_def 
                     ex_graphT'_def ex_loc_assT_def ex_loc_assT'_def shopT_def pubT_def ex_credsT_def
                     ex_credsT'_def ex_credsT''_def)
    apply (rule conjI)
     apply (rule ext, simp add: insert_Diff_if shopT_def pubT_def)
    apply (simp add: ex_efidsT_def ex_efidsT'_def shopT_def pubT_def ex_credsT_def)
    apply (rule conjI)
     apply force
    by (rule ext, simp add: insert_Diff_if shopT_def pubT_def)
qed

lemma step2r: "corona_scenarioT'  \<rightarrow>\<^sub>n* corona_scenarioT''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioT', corona_scenarioT'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

lemma step3: "corona_scenarioT''  \<rightarrow>\<^sub>n corona_scenarioT'''"
proof (rule_tac l' = shopT and l = pubT and a = "''Eve''" in move, rule refl)
  show "''Eve'' @\<^bsub>graphI corona_scenarioT''\<^esub> pubT"
   by (simp add: corona_scenarioT''_def ex_graphT''_def pubT_def shopT_def atI_def ex_loc_assT'_def)
next show \<open>pubT \<in> nodes (graphI corona_scenarioT'')\<close>
    by (simp add: corona_scenarioT''_def pubT_def ex_graphT''_def nodes_def, blast)
next show \<open>shopT \<in> nodes (graphI corona_scenarioT'')\<close>
    by (simp add: corona_scenarioT''_def pubT_def ex_graphT''_def nodes_def, blast)
next show \<open>''Eve'' \<in> actors_graph (graphI corona_scenarioT'')\<close>
    by (simp add: actors_graph_def corona_scenarioT''_def ex_graphT''_def nodes_def ex_loc_assT'_def 
                  shopT_def pubT_def, blast)
next show \<open>enables corona_scenarioT'' shopT (Actor ''Eve'') move\<close>
    by (simp add: enables_def corona_scenarioT''_def local_policiesT_def)
next show \<open>corona_scenarioT''' =
    Infrastructure (move_graph_a ''Eve'' pubT shopT (graphI corona_scenarioT'')) (delta corona_scenarioT'')\<close>
    apply (simp add: corona_scenarioT'''_def ex_graphT'''_def move_graph_a_def pubT_def shopT_def
                     corona_scenarioT''_def ex_graphT''_def ex_loc_assT''_def ex_loc_assT'_def)
    apply (rule conjI)
     apply (rule ext, simp add: insert_Diff_if shopT_def pubT_def)+
    apply (rule conjI)
    apply (simp add: ex_credsT'_def ex_credsT''_def)
     apply force
    by (rule ext, simp add: ex_efidsT'_def ex_efidsT''_def ex_credsT'_def insert_Diff_if shopT_def pubT_def)
qed

lemma step3r: "corona_scenarioT''  \<rightarrow>\<^sub>n* corona_scenarioT'''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioT'', corona_scenarioT''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step3, auto)
qed

lemma step4: "corona_scenarioT'''  \<rightarrow>\<^sub>n corona_scenarioT''''"
proof (rule_tac l = shopT and a = "''Eve''" in get, rule refl)
  show \<open>''Eve'' @\<^bsub>graphI corona_scenarioT'''\<^esub> shopT\<close>
   by (simp add: corona_scenarioT'''_def ex_graphT'''_def pubT_def shopT_def atI_def ex_loc_assT''_def)
next show \<open>enables corona_scenarioT''' shopT (Actor ''Eve'') get\<close>
    by (simp add: enables_def corona_scenarioT'''_def local_policiesT_def)
next show "shopT \<in> nodes (graphI corona_scenarioT''')"
    using corona_scenarioT'''_def ex_graphT'''_def nodes_def by auto
next show \<open>corona_scenarioT'''' =
    Infrastructure
     (Lgraph (gra (graphI corona_scenarioT''')) (agra (graphI corona_scenarioT''')) (cgra (graphI corona_scenarioT'''))
       (lgra (graphI corona_scenarioT''')) (egra (graphI corona_scenarioT'''))
       ((kgra (graphI corona_scenarioT'''))
        (''Eve'' := (kgra (graphI corona_scenarioT''') (''Eve''))
           (shopT := {(x, y). x \<in> agra (graphI corona_scenarioT''') shopT \<and> y \<in> egra (graphI corona_scenarioT''') shopT}))))
     (delta corona_scenarioT''') \<close>
    apply (simp add: corona_scenarioT'''_def ex_graphT'''_def move_graph_a_def pubT_def shopT_def
                     corona_scenarioT''''_def ex_graphT''''_def ex_loc_assT''_def ex_loc_assT'_def)
     apply (rule ext, simp add: insert_Diff_if shopT_def pubT_def)+
    apply (simp add: ex_efidsT''_def shopT_def pubT_def ex_knosT'_def ex_knosT''_def)
    apply (rule impI, rule ext)
    apply (simp add: insert_Diff_if shopT_def pubT_def)
    apply (rule impI)+
    apply (rule equalityI)
     apply (rule subsetI)
     apply (case_tac xa)
    apply simp
    apply linarith
     apply (rule subsetI)
     apply (case_tac xa)
    apply simp
    by metis
qed

lemma step4r: "corona_scenarioT'''  \<rightarrow>\<^sub>n* corona_scenarioT''''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioT''', corona_scenarioT'''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step4, auto)
qed

(* The refinements for the previous attack still work *)
lemma corona_refT: "[\<N>\<^bsub>(IcoronaT,scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaT,CoronaT')\<^esub>, \<N>\<^bsub>(CoronaT',CoronaT'')\<^esub>,  \<N>\<^bsub>(CoronaT'',CoronaT''')\<^esub>, \<N>\<^bsub>(CoronaT''',scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup>)"
  by (metis append_Cons append_Nil refI)  

lemma corona_refT': "[\<N>\<^bsub>(IcoronaT,scoronaT')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT')\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaT,CoronaT')\<^esub>, \<N>\<^bsub>(CoronaT',CoronaT'')\<^esub>,  \<N>\<^bsub>(CoronaT'',CoronaT''')\<^esub>, \<N>\<^bsub>(CoronaT''',scoronaT')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT')\<^esup>)"
  by (metis append_Cons append_Nil refI)  


lemma att_coronaT: "\<turnstile>([\<N>\<^bsub>(IcoronaT,CoronaT')\<^esub>, \<N>\<^bsub>(CoronaT',CoronaT'')\<^esub>,  \<N>\<^bsub>(CoronaT'',CoronaT''')\<^esub>, \<N>\<^bsub>(CoronaT''',scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup>)"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(IcoronaT, CoronaT')\<^esub>"
    apply (simp add: IcoronaT_def CoronaT'_def att_base)
    using state_transition_infra_def step1 by blast
next show \<open> \<turnstile>[\<N>\<^bsub>(CoronaT', CoronaT'')\<^esub>, \<N>\<^bsub>(CoronaT'', CoronaT''')\<^esub>, \<N>\<^bsub>(CoronaT''', scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(CoronaT', scoronaT)\<^esup>\<close>
    apply (subst att_and, simp)
    apply (rule conjI)
     apply (simp add: CoronaT'_def CoronaT''_def att_base state_transition_infra_def step2)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: CoronaT''_def CoronaT'''_def att_base state_transition_infra_def step3)
    apply (subst att_and, simp)
    apply (simp add: CoronaT'''_def scoronaT_def att_base state_transition_infra_def step4)
    apply (rule_tac x = "corona_scenarioT''''" in exI)
    apply (rule conjI)
     prefer 2
    apply (rule step4)
     apply (unfold corona_scenarioT''''_def global_policyT''_def)
     apply (unfold global_policyT''_def identifiableT'_def ex_graphT''''_def ex_loc_assT''_def nodes_def is_singleton_def
                  ex_efidsT''_def pubT_def shopT_def ex_credsT_def ex_locsT_def ex_knosT''_def local_policiesT_def)
    apply (rule_tac x = 3 in exI, simp)
    oops
(* Here the proof following the outline of the previous step fails and that is what we want to show 
   here (so it is intentional showing that the "old" attack is now indeed eliminated. But there is 
   a new one (see below).
proof (prove)
goal (1 subgoal):
 1. False

remaining steps would have been:
     apply (rule conjI)
    apply (rule impI)
     apply (rule_tac x = "''Bob''" in exI)
      apply (rule_tac  x = "Efid 3" in exI)
      apply (rule equalityI)
          apply auto[1]
      apply simp
by blast
qed


lemma corona_abs_attT: "\<turnstile>\<^sub>V([\<N>\<^bsub>(IcoronaT,scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup>)"
  oops

lemma corona_attT: "corona_KripkeT \<turnstile> EF {x. \<exists> n. \<not>(global_policyT'' x (Efid n))}"
  oops

theorem corona_EFT: "corona_KripkeT \<turnstile> EF scoronaT"
  oops

theorem corona_ATT: "\<exists> A. \<turnstile> A \<and> attack A = (IcoronaT,scoronaT)"
  oops

theorem corona_EFT': "corona_KripkeT \<turnstile> EF scoronaT"
  oops

(* We can already show security for global_policy'' *)
lemma kgra_disj_imp_not_identifiable: 
"''Eve'' \<in>  actors_graph  (graphI I) \<Longrightarrow>
\<exists> l \<in> nodes (graphI I). \<exists> l' \<in> nodes (graphI I). l \<noteq> l' \<Longrightarrow>
(\<forall> a \<in> actors_graph  (graphI I).
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
         (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {})))
\<Longrightarrow> global_policyT'' I eid "
  apply (simp add: global_policyT''_def identifiableT'_def)
  apply (erule bexE)+
  apply (subgoal_tac "{(Id, Eid).
            (\<forall>x\<in>InfrastructureTwo.nodes (InfrastructureTwo.graphI I).
                (Id, Eid) \<in> InfrastructureTwo.kgra (InfrastructureTwo.graphI I) ''Eve'' x) \<and>
            Id \<noteq> ''Eve'' \<and> Eid = eid} = {}")
   apply (erule ssubst)
   apply (simp add: is_singleton_def)
  by (smt (verit, ccfv_threshold) IntI case_prodI2 case_prod_conv empty_Collect_eq empty_iff split_part)
(* The above theorem can be generalized for any reachable I since the preconditions are preserved
   (see the standard procdure for other invariants) *)

theorem RR_cycle_succeeds: "corona_KripkeT \<turnstile> AG {x. \<forall> n. global_policyT'' x (Efid n)}"

  oops
*)

(* Instead we now find the alternative attack where Bob is left on his own with Eve in the pub*)
(* The steps for the isolation attack where Alice leaves and then Eve does a get *)
lemma step1i: "corona_scenarioT  \<rightarrow>\<^sub>n corona_scenarioTi"
proof (rule_tac l = pubT and l' = shopT and a = "''Alice''" in move)
  show "graphI corona_scenarioT = graphI corona_scenarioT" by (rule refl)
next show "''Alice'' @\<^bsub>InfrastructureTwo.graphI corona_scenarioT\<^esub> pubT" 
    by (simp add: corona_scenarioT_def ex_graphT_def ex_loc_assT_def atI_def nodes_def)
next show "pubT \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT)"
    by (simp add: pubT_def shopT_def corona_scenarioT_def ex_graphT_def ex_loc_assT_def atI_def nodes_def)
next show "shopT \<in> InfrastructureTwo.nodes (InfrastructureTwo.graphI corona_scenarioT)"
    by (simp add: pubT_def shopT_def corona_scenarioT_def ex_graphT_def ex_loc_assT_def atI_def nodes_def)
next show "''Alice'' \<in> InfrastructureTwo.actors_graph (InfrastructureTwo.graphI corona_scenarioT)"
    by (simp add: pubT_def shopT_def corona_scenarioT_def ex_graphT_def ex_loc_assT_def ex_knosT_def 
           ex_credsT_def ex_locsT_def ex_efidsT_def InfrastructureTwo.actors_graph_def nodes_def, blast)
next show "InfrastructureTwo.enables corona_scenarioT shopT (Actor ''Alice'') move"
    by (simp add: enables_def corona_scenarioT_def ex_graphT_def local_policiesT_def
                    ex_credsT_def ex_locsT_def)
next show "corona_scenarioTi =
    InfrastructureTwo.infrastructure.Infrastructure
     (InfrastructureTwo.move_graph_a ''Alice'' pubT shopT (InfrastructureTwo.graphI corona_scenarioT))
     (InfrastructureTwo.delta corona_scenarioT)"
    apply (simp add: corona_scenarioTi_def ex_graphTi_def move_graph_a_def 
                     corona_scenarioT_def ex_graphT_def pubT_def shopT_def 
                     ex_loc_assTi_def ex_loc_assT_def ex_efidsTi_def ex_efidsT_def 
                     ex_knosT_def ex_knosTi_def ex_credsT_def ex_credsTi_def)
    apply (rule conjI)
     apply (rule ext, simp add: insert_Diff_if shopT_def pubT_def)
    apply (rule conjI)
    apply (rule ext, simp)
    by (rule ext, simp add: shopT_def)
qed

lemma step1ir: "corona_scenarioT  \<rightarrow>\<^sub>n* corona_scenarioTi"
proof (simp add: state_transition_in_refl_def)
  show " (corona_scenarioT, corona_scenarioTi) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1i, auto)
qed

lemma step2i: "corona_scenarioTi  \<rightarrow>\<^sub>n corona_scenarioTii"
proof (rule_tac l = pubT  and a = "''Eve''" in get, rule refl)
  show "''Eve'' @\<^bsub>InfrastructureTwo.graphI corona_scenarioTi\<^esub> pubT"
   by (simp add: corona_scenarioTi_def ex_graphTi_def pubT_def shopT_def atI_def ex_loc_assT_def ex_loc_assTi_def)
next show "pubT \<in> nodes (graphI corona_scenarioTi)"
    by (simp add: corona_scenarioTi_def ex_graphTi_def pubT_def atI_def nodes_def, blast)
next show "enables corona_scenarioTi pubT (Actor ''Eve'') get"
    by (simp add: enables_def corona_scenarioTi_def local_policiesT_def)
next show "corona_scenarioTii =
    InfrastructureTwo.infrastructure.Infrastructure
     (InfrastructureTwo.igraph.Lgraph (InfrastructureTwo.gra (InfrastructureTwo.graphI corona_scenarioTi))
       (InfrastructureTwo.agra (InfrastructureTwo.graphI corona_scenarioTi))
       (InfrastructureTwo.cgra (InfrastructureTwo.graphI corona_scenarioTi))
       (InfrastructureTwo.lgra (InfrastructureTwo.graphI corona_scenarioTi))
       (InfrastructureTwo.egra (InfrastructureTwo.graphI corona_scenarioTi))
       ((InfrastructureTwo.kgra (InfrastructureTwo.graphI corona_scenarioTi))
        (''Eve'' := (InfrastructureTwo.kgra (InfrastructureTwo.graphI corona_scenarioTi) ''Eve'')
           (pubT :=
              {(x, y).
               x \<in> InfrastructureTwo.agra (InfrastructureTwo.graphI corona_scenarioTi) pubT \<and>
               y \<in> InfrastructureTwo.egra (InfrastructureTwo.graphI corona_scenarioTi) pubT}))))
     (InfrastructureTwo.delta corona_scenarioTi)"
    apply (simp add: corona_scenarioTi_def ex_graphTii_def move_graph_a_def corona_scenarioTii_def 
                     ex_graphTi_def ex_loc_assT_def ex_loc_assTi_def shopT_def pubT_def ex_credsT_def
                     ex_credsTi_def ex_knosT_def ex_knosTi_def ex_efidsTi_def)
    apply (rule ext, simp add: insert_Diff_if shopT_def pubT_def)
    apply (rule impI)
    by (rule ext, force)
qed

lemma step2ir: "corona_scenarioTi  \<rightarrow>\<^sub>n* corona_scenarioTii"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioTi, corona_scenarioTii) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2i, auto)
qed

lemma corona_refTi: "[\<N>\<^bsub>(IcoronaT,scoronaT')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT')\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaT,CoronaTi)\<^esub>,  \<N>\<^bsub>(CoronaTi,scoronaT')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT')\<^esup>)"
  by (metis append_Cons append_Nil refI)  


lemma att_coronaTi: "\<turnstile>([\<N>\<^bsub>(IcoronaT,CoronaTi)\<^esub>, \<N>\<^bsub>(CoronaTi,scoronaT')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT')\<^esup>)"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(IcoronaT, CoronaTi)\<^esub>"
 apply (simp add: IcoronaT_def CoronaTi_def att_base)
    using state_transition_infra_def step1i by blast
next show " \<turnstile>[\<N>\<^bsub>(CoronaTi, scoronaT')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(CoronaTi, scoronaT')\<^esup>"
apply (subst att_and, simp)
     apply (simp add: CoronaTi_def CoronaTii_def att_base state_transition_infra_def step2i)
    apply (simp add: CoronaTi_def CoronaTii_def scoronaT'_def  att_base state_transition_infra_def step2i)
    apply (rule_tac x = "corona_scenarioTii" in exI)
    apply (rule conjI)
     prefer 2
    apply (rule step2i)
    apply (simp add: global_policyT_def corona_scenarioTii_def ex_graphTii_def ex_efidsTi_def
                     identifiableT'_def is_singleton_def nodes_def
                     ex_knosTi_def pubT_def shopT_def)
    apply (rule_tac  x = "3" in exI)
 apply (rule set_exI)
     prefer 2
    apply (subgoal_tac 
    "{Location 0} \<subseteq> {x. \<exists>y. x = Location 0 \<and> y = Location (Suc 0) \<or> y = Location 0 \<and> x = Location (Suc 0)}")
      apply assumption
    apply simp
     apply (rule_tac x = "''Bob''" in exI)
      apply (rule_tac  x = "Efid 3" in exI)
      apply (rule equalityI)
     apply simp
     apply auto[1]
    apply (rule subsetI)
    apply (rule CollectI)
      apply (case_tac x)
by simp
qed

(* We can already establish non-identifiability for subsets L with more than 2 elements.
   This should follow simply from disjointness of the kgra set intersections for all pairs of 
   locations. *)
lemma all_kgra_disj_imp_greater_two_inv: "(\<forall> a \<in> actors_graph (graphI y). 
     (\<forall> l \<in> nodes (graphI I). \<forall> l' \<in> nodes (graphI I). 
      (l \<noteq> l' \<longrightarrow> (kgra (graphI I) a l) \<inter> kgra(graphI I) a l' = {}))) \<Longrightarrow>
      L \<subseteq> nodes(graphI I)  \<Longrightarrow> card L \<ge> 2 \<Longrightarrow> 
      (\<not>(identifiableT' eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L))
                          - {(x,y). x = ''Eve''})))"
  oops

end
end
