theory CoronaAppTwo
  imports InfrastructureTwo
begin
locale scenarioCoronaTwo = scenarioCoronaOne +

fixes corona_actorsT :: "identity set"
defines corona_actorsT_def: "corona_actorsT \<equiv> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve''}"

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

(* This version is apparently different from the below global_policy'' where we use the image operator
fixes global_policy' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy'_def: "global_policy' I eid \<equiv>  
             \<not>(identifiable' eid 
                ((\<Inter> {A. (\<exists> l \<in> nodes(graphI I). (A = (kgra(graphI I)(Actor ''Eve'') l)))})
                 - {(x,y). x = ''Eve''}))"
*)

fixes global_policyT'' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyT''_def: "global_policyT'' I eid \<equiv>  
             \<not>(identifiableT' eid 
                ((\<Inter> (kgra(graphI I)(Actor ''Eve'')`(nodes(graphI I))))
                 - {(x,y). x = ''Eve''}))"

fixes ex_credsT :: "identity \<Rightarrow> (string set * string set * efidlist)"
defines ex_credsT_def: 
          "ex_credsT \<equiv> (\<lambda> x. if x = ''Alice'' then ({}, {}, 
                              Efids (Efid 1) 0 [Efid 11, Efid 21, Efid 31, Efid 41]) else 
                            (if x = ''Bob'' then  ({},{}, 
                              Efids (Efid 2) 0 [Efid 12, Efid 22, Efid 32, Efid 42]) else 
                            (if x = ''Charly'' then ({},{}, 
                              Efids (Efid 3) 0 [Efid 13, Efid 23, Efid 33, Efid 43]) else
                            (if x = ''David'' then ({},{}, 
                              Efids (Efid 4) 0 [Efid 14, Efid 24, Efid 34, Efid 44]) else
                            (if x = ''Eve'' then ({},{}, 
                              Efids (Efid 5) 0 [Efid 15, Efid 25, Efid 35, Efid 35]) else 
                                 ({},{}, Efids (Efid 0) 0 [Efid 10, Efid 20, Efid 30, Efid 40]))))))"

fixes ex_locsT :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locsT \<equiv> (\<lambda> x. ('''',{}))"

fixes ex_loc_assT :: "location \<Rightarrow> identity set"
defines ex_loc_assT_def: "ex_loc_assT \<equiv>
          (\<lambda> x. if x = pubT then {''Alice'', ''Bob'', ''Eve''}  
                 else (if x = shopT then {''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_assT' :: "location \<Rightarrow> identity set"
defines ex_loc_assT'_def: "ex_loc_assT' \<equiv>
          (\<lambda> x. if x = pubT then {''Alice'', ''Eve''}  
                 else (if x = shopT then { ''Bob'', ''Charly'', ''David''} 
                       else {}))"
fixes ex_loc_assT'' :: "location \<Rightarrow> identity set"
defines ex_loc_assT''_def: "ex_loc_assT'' \<equiv>
          (\<lambda> x. if x = pubT then {''Alice''}  
                 else (if x = shopT then {''Eve'', ''Bob'', ''Charly'', ''David''} 
                       else {}))"

fixes ex_efidsT :: "location \<Rightarrow> efid set"
defines ex_efidsT_def: "ex_efidsT \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 11, Efid 12, Efid 15}
                else (if x = shopT then {Efid 13, Efid 14}
                      else {}))"

fixes ex_efidsT' :: "location \<Rightarrow> efid set"
defines ex_efidsT'_def: "ex_efidsT' \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 11, Efid 15}
                else (if x = shopT then {Efid 12, Efid 13, Efid 14}
                      else {}))"

fixes ex_efidsT'' :: "location \<Rightarrow> efid set"
defines ex_efidsT''_def: "ex_efidsT'' \<equiv> 
          (\<lambda> x. if x = pubT then {Efid 11}
                else (if x = shopT then {Efid 15, Efid 12, Efid 13, Efid 14}
                      else {}))"

fixes ex_knosT :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosT_def: "ex_knosT \<equiv> (\<lambda> x :: actor. 
                  (if x = Actor ''Eve'' then (\<lambda> l :: location. {} :: (identity * efid) set) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosT' :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosT'_def: "ex_knosT' \<equiv> (\<lambda> x :: actor. 
                  (if x = Actor ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubT then 
                                  ({(''Alice'', Efid 11),(''Alice'', Efid 12),(''Alice'', Efid 15),
                                    (''Bob'', Efid 11),(''Bob'', Efid 12),(''Bob'', Efid 15),
                                    (''Eve'', Efid 11),(''Eve'', Efid 12),(''Eve'', Efid 15)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosT'' :: "actor \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosT''_def: "ex_knosT'' \<equiv> (\<lambda> x :: actor.                       
                  (if x = Actor ''Eve'' then 
                      (\<lambda> l :: location.
                           (if l = pubT then 
                                  ({(''Alice'', Efid 11),(''Alice'', Efid 12),(''Alice'', Efid 15),
                                    (''Bob'', Efid 11),(''Bob'', Efid 12),(''Bob'', Efid 15),
                                    (''Eve'', Efid 11),(''Eve'', Efid 12),(''Eve'', Efid 15)})
                            else (if l = shopT then 
                                     ({(''Eve'', Efid 15),(''Eve'', Efid 12),(''Eve'', Efid 13),(''Eve'', Efid 14),
                                       (''Bob'', Efid 15),(''Bob'', Efid 12),(''Bob'', Efid 13),(''Bob'', Efid 14), 
                                       (''Charly'', Efid 15),(''Charly'', Efid 12),(''Charly'', Efid 13),(''Charly'', Efid 14),
                                       (''David'', Efid 15),(''David'', Efid 12),(''David'', Efid 13),(''David'', Efid 14)})
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

(* initial *)
fixes ex_graphT :: "igraph"
defines ex_graphT_def: "ex_graphT \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT ex_credsT ex_locsT ex_efidsT ex_knosT"

(* Eve gets the ex_knos *)
fixes ex_graphT' :: "igraph"
defines ex_graphT'_def: "ex_graphT' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT ex_credsT ex_locsT ex_efidsT ex_knosT'"

(* Bob goes to shop *)
fixes ex_graphT'' :: "igraph"
defines ex_graphT''_def: "ex_graphT'' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT' ex_credsT ex_locsT ex_efidsT' ex_knosT'"

(* Eve goes to shop *)
fixes ex_graphT''' :: "igraph"
defines ex_graphT'''_def: "ex_graphT''' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT'' ex_credsT ex_locsT ex_efidsT'' ex_knosT'"

(* Eve gets ex_knos at shop *)
fixes ex_graphT'''' :: "igraph"
defines ex_graphT''''_def: "ex_graphT'''' \<equiv> Lgraph {(pubT, shopT)} ex_loc_assT'' ex_credsT ex_locsT ex_efidsT'' ex_knosT''"

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

fixes local_policiesT :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesT_def: "local_policiesT G \<equiv> 
    (\<lambda> x. if x = pubT then  {(\<lambda> y. True, {get,move})}
          else (if x = shopT then {(\<lambda> y. True, {get,move})} 
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
defines Corona''_def: "CoronaT'' \<equiv> {corona_scenarioT''}"
fixes corona_scenarioT''' :: "infrastructure"
defines corona_scenarioT'''_def: "corona_scenarioT''' \<equiv> Infrastructure ex_graphT''' local_policiesT"
fixes CoronaT''' :: "infrastructure set"
defines CoronaT'''_def: "CoronaT''' \<equiv> {corona_scenarioT'''}"
fixes corona_scenarioT'''' :: "infrastructure"
defines corona_scenarioT''''_def: "corona_scenarioT'''' \<equiv> Infrastructure ex_graphT'''' local_policiesT"
fixes CoronaT'''' :: "infrastructure set"
defines CoronaT''''_def: "CoronaT'''' \<equiv> {corona_scenarioT''''}"

fixes corona_statesT
defines corona_statesT_def: "corona_statesT \<equiv> { I. corona_scenarioT \<rightarrow>\<^sub>i* I }"
fixes corona_KripkeT
defines "corona_KripkeT \<equiv> Kripke corona_statesT IcoronaT"
fixes scoronaT 
defines "scoronaT \<equiv> {x. \<exists> n. \<not> global_policyT'' x (Efid n)}"  

begin

lemma refmapTwo_lem: "\<forall>s::InfrastructureTwo.infrastructure.
       (Corona_scenarioT, s) \<in> {(x::InfrastructureTwo.infrastructure, y::InfrastructureTwo.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::InfrastructureTwo.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapT s \<rightarrow>\<^sub>n rmapT s')"
  oops

theorem refmapTwo: "corona_KripkeO \<sqsubseteq>\<^sub>rmapT corona_KripkeT"
  oops

lemma step1: "corona_scenarioT  \<rightarrow>\<^sub>n corona_scenarioT'"
  oops

lemma step1r: "corona_scenarioT  \<rightarrow>\<^sub>n* corona_scenarioT'"
  oops

lemma step2: "corona_scenarioT'  \<rightarrow>\<^sub>n corona_scenarioT''"
  oops

lemma step2r: "corona_scenarioT'  \<rightarrow>\<^sub>n* corona_scenarioT''"
  oops

lemma step3: "corona_scenarioT''  \<rightarrow>\<^sub>n corona_scenarioT'''"
  oops

lemma step3r: "corona_scenarioT''  \<rightarrow>\<^sub>n* corona_scenarioT'''"
  oops

lemma step4: "corona_scenarioT'''  \<rightarrow>\<^sub>n corona_scenarioT''''"
  oops

lemma step4r: "corona_scenarioT'''  \<rightarrow>\<^sub>n* corona_scenarioT''''"
  oops

lemma corona_refT: "[\<N>\<^bsub>(IcoronaT,scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaT,CoronaT')\<^esub>, \<N>\<^bsub>(CoronaT',CoronaT'')\<^esub>,  \<N>\<^bsub>(CoronaT'',CoronaT''')\<^esub>, \<N>\<^bsub>(CoronaT''',scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup>)"
  oops

lemma att_coronaT: "\<turnstile>([\<N>\<^bsub>(IcoronaT,CoronaT')\<^esub>, \<N>\<^bsub>(CoronaT',CoronaT'')\<^esub>,  \<N>\<^bsub>(CoronaT'',CoronaT''')\<^esub>, \<N>\<^bsub>(CoronaT''',scoronaT)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaT,scoronaT)\<^esup>)"
  oops

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

end
end
