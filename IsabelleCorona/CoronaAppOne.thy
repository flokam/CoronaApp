theory CoronaAppOne
  imports InfrastructureOne
begin
locale scenarioCoronaOne = scenarioCorona +

  fixes corona_actorsO :: "identity set"
defines corona_actorsO_def: "corona_actorsO \<equiv> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}"

fixes corona_locationsO :: "location set"
defines corona_locationsO_def: "corona_locationsO \<equiv> {Location 0, Location 1}"
fixes pubO :: "location"
defines pubO_def: "pubO \<equiv> Location 0"
fixes shopO :: "location"
defines shopO_def: "shopO \<equiv> Location 1"

(* not relevant any more. It was made for earlier versions where the intersection happened
   implicitly in the semantics. 
fixes identifiable :: "[infrastructure,actor,efid, location] \<Rightarrow> bool"
defines identifiable_def: "identifiable I a eid l\<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> kgra (graphI I) a l \<and> Eid = eid}"
fixes global_policy :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy_def: "global_policy I eid \<equiv>  (\<exists> l. \<not>(identifiable I (Actor ''Eve'') eid l))"
*)

fixes identifiableO' :: "[efid, (identity * efid)set] \<Rightarrow> bool"
defines identifiableO'_def: "identifiableO' eid A \<equiv> is_singleton{(Id,Eid). (Id, Eid) \<in> A \<and> Eid = eid}"

(* This version is apparently different from the below global_policy'' where we use the image operator
fixes global_policy' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policy'_def: "global_policy' I eid \<equiv>  
             \<not>(identifiable' eid 
                ((\<Inter> {A. (\<exists> l \<in> nodes(graphI I). (A = (kgra(graphI I)(Actor ''Eve'') l)))})
                 - {(x,y). x = ''Eve''}))"
*)

fixes global_policyO'' :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyO''_def: "global_policyO'' I eid \<equiv>  
             \<not>(identifiableO' eid 
                ((\<Inter> (kgra(graphI I)(''Eve'')`(nodes(graphI I))))
                 - {(x,y). x = ''Eve''}))"

fixes global_policyO :: "[infrastructure, efid] \<Rightarrow> bool"
defines global_policyO_def: "global_policyO I eid \<equiv>  
             \<forall> L. L \<subseteq> nodes(graphI I) \<longrightarrow> (\<not>(identifiableO' eid 
               ((\<Inter> (kgra(graphI I)(''Eve'')`L))
                          - {(x,y). x = ''Eve''})))"

fixes ex_credsO :: "identity \<Rightarrow> efidlist"
defines ex_credsO_def: 
          "ex_credsO \<equiv> (\<lambda> x. if x = ''Alice'' then (Efids (Efid 1) 0 (\<lambda> n. Efid (2^(n+1)))) else 
                            (if x = ''Bob'' then  (Efids (Efid 2) 0 (\<lambda> n. Efid (3^(n+1)))) else 
                            (if x = ''Charly'' then (Efids (Efid 3) 0 (\<lambda> n. Efid (5^(n+1)))) else
                            (if x = ''David'' then (Efids (Efid 4) 0 (\<lambda> n. Efid (7^(n+1)))) else
                            (if x = ''Eve'' then (Efids (Efid 5) 0 (\<lambda> n. Efid (11^(n+1)))) else 
                            (if x = ''Flo'' then (Efids (Efid 6) 0 (\<lambda> n. Efid (13^(n+1)))) else 
                                 (Efids (Efid 0) 0 (\<lambda> n. Efid (17^(n+1))))))))))"

fixes ex_locsO :: "location \<Rightarrow> string * (dlm * data) set"
defines "ex_locsO \<equiv> (\<lambda> x. ('''',{}))"

fixes ex_loc_assO :: "location \<Rightarrow> identity set"
defines ex_loc_assO_def: "ex_loc_assO \<equiv>
          (\<lambda> x. if x = pubO then {''Alice'', ''Bob'', ''Eve''}  
                 else (if x = shopO then {''Charly'', ''David'', ''Flo''} 
                       else {}))"
fixes ex_loc_assO' :: "location \<Rightarrow> identity set"
defines ex_loc_assO'_def: "ex_loc_assO' \<equiv>
          (\<lambda> x. if x = pubO then {''Alice'', ''Eve''}  
                 else (if x = shopO then { ''Bob'', ''Charly'', ''David'', ''Flo''} 
                       else {}))"
fixes ex_loc_assO'' :: "location \<Rightarrow> identity set"
defines ex_loc_assO''_def: "ex_loc_assO'' \<equiv>
          (\<lambda> x. if x = pubO then {''Alice''}  
                 else (if x = shopO then {''Eve'', ''Bob'', ''Charly'', ''David'', ''Flo''} 
                       else {}))"

fixes ex_efidsO :: "location \<Rightarrow> efid set"
defines ex_efidsO_def: "ex_efidsO \<equiv> 
          (\<lambda> x. if x = pubO then {Efid 2, Efid 3, Efid 11}
                else (if x = shopO then {Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_efidsO' :: "location \<Rightarrow> efid set"
defines ex_efidsO'_def: "ex_efidsO' \<equiv> 
          (\<lambda> x. if x = pubO then {Efid 2, Efid 11}
                else (if x = shopO then {Efid 3, Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_efidsO'' :: "location \<Rightarrow> efid set"
defines ex_efidsO''_def: "ex_efidsO'' \<equiv> 
          (\<lambda> x. if x = pubO then {Efid 2}
                else (if x = shopO then {Efid 11, Efid 3, Efid 5, Efid 7, Efid 13}
                      else {}))"

fixes ex_knosO :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosO_def: "ex_knosO \<equiv> (\<lambda> x :: identity. 
                  (if x = ''Eve'' then (\<lambda> l :: location. {} :: (identity * efid) set) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosO' :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosO'_def: "ex_knosO' \<equiv> (\<lambda> x :: identity. 
                  (if x = ''Eve'' then 
                     (\<lambda> l :: location.
                        (if l = pubO then 
                                  ({(''Alice'', Efid 2),(''Alice'', Efid 3),(''Alice'', Efid 11),
                                    (''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 11)})
                         else {})) 
                   else (\<lambda> l :: location. {} :: (identity * efid) set)))"

fixes ex_knosO'' :: "identity \<Rightarrow> location \<Rightarrow> (identity * efid) set"
defines ex_knosO''_def: "ex_knosO'' \<equiv> (\<lambda> x :: identity.                       
                  (if x = ''Eve'' then 
                      (\<lambda> l :: location.
                           (if l = pubO then 
                                  ({(''Alice'', Efid 2),(''Alice'', Efid 3),(''Alice'', Efid 11),
                                    (''Bob'', Efid 2),(''Bob'', Efid 3),(''Bob'', Efid 11),
                                    (''Eve'', Efid 2),(''Eve'', Efid 3),(''Eve'', Efid 11)})
                            else (if l = shopO then 
                                     ({(''Eve'', Efid 11),(''Eve'', Efid 3),(''Eve'', Efid 5),(''Eve'', Efid 7), (''Eve'', Efid 13),
                                       (''Bob'', Efid 11),(''Bob'', Efid 3),(''Bob'', Efid 5),(''Bob'', Efid 7), (''Bob'', Efid 13),
                                       (''Charly'', Efid 11),(''Charly'', Efid 3),(''Charly'', Efid 5),(''Charly'', Efid 7), (''Charly'', Efid 13),
                                       (''David'', Efid 11),(''David'', Efid 3),(''David'', Efid 5),(''David'', Efid 7), (''David'', Efid 13),
                                       (''Flo'', Efid 11),(''Flo'', Efid 3),(''Flo'', Efid 5),(''Flo'', Efid 7), (''Flo'', Efid 13)
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

(* initial *)
fixes ex_graphO :: "igraph"
defines ex_graphO_def: "ex_graphO \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO ex_credsO ex_locsO ex_efidsO ex_knosO"

(* Eve gets the ex_knos *)
fixes ex_graphO' :: "igraph"
defines ex_graphO'_def: "ex_graphO' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO ex_credsO ex_locsO ex_efidsO ex_knosO'"

(* Bob goes to shop *)
fixes ex_graphO'' :: "igraph"
defines ex_graphO''_def: "ex_graphO'' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO' ex_credsO ex_locsO ex_efidsO' ex_knosO'"

(* Eve goes to shop *)
fixes ex_graphO''' :: "igraph"
defines ex_graphO'''_def: "ex_graphO''' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO'' ex_credsO ex_locsO ex_efidsO'' ex_knosO'"

(* Eve gets ex_knos at shop *)
fixes ex_graphO'''' :: "igraph"
defines ex_graphO''''_def: "ex_graphO'''' \<equiv> Lgraph {(pubO, shopO)} ex_loc_assO'' ex_credsO ex_locsO ex_efidsO'' ex_knosO''"

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

fixes local_policiesO :: "[igraph, location] \<Rightarrow> policy set"
defines local_policiesO_def: "local_policiesO G \<equiv> 
    (\<lambda> x. if x = pubO then  {(\<lambda> y. True, {get,move,put})}
          else (if x = shopO then {(\<lambda> y. True, {get,move,put})} 
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

fixes rmapO :: "InfrastructureOne.infrastructure \<Rightarrow> Infrastructure.infrastructure"
defines rmapO_def:
"rmapO I \<equiv> InfrastructureOne.ref_map I local_policies"

fixes corona_scenarioO :: "infrastructure"
defines corona_scenarioO_def:
"corona_scenarioO \<equiv> Infrastructure ex_graphO local_policiesO"
fixes IcoronaO :: "infrastructure set"
defines IcoronaO_def:
  "IcoronaO \<equiv> {corona_scenarioO}"

(* other states of scenario *)
(* First step: Bob goes to shop *)

fixes corona_scenarioO' :: "infrastructure"
defines corona_scenarioO'_def: "corona_scenarioO' \<equiv> Infrastructure ex_graphO' local_policiesO"
fixes CoronaO' :: "infrastructure set"
defines CoronaO'_def: "CoronaO' \<equiv> {corona_scenarioO'}"
fixes corona_scenarioO'' :: "infrastructure"
defines corona_scenarioO''_def: "corona_scenarioO'' \<equiv> Infrastructure ex_graphO'' local_policiesO"
fixes CoronaO'' :: "infrastructure set"
defines CoronaO''_def: "CoronaO'' \<equiv> {corona_scenarioO''}"
fixes corona_scenarioO''' :: "infrastructure"
defines corona_scenarioO'''_def: "corona_scenarioO''' \<equiv> Infrastructure ex_graphO''' local_policiesO"
fixes CoronaO''' :: "infrastructure set"
defines CoronaO'''_def: "CoronaO''' \<equiv> {corona_scenarioO'''}"
fixes corona_scenarioO'''' :: "infrastructure"
defines corona_scenarioO''''_def: "corona_scenarioO'''' \<equiv> Infrastructure ex_graphO'''' local_policiesO"
fixes CoronaO'''' :: "infrastructure set"
defines CoronaO''''_def: "CoronaO'''' \<equiv> {corona_scenarioO''''}"

fixes corona_statesO
defines corona_statesO_def: "corona_statesO \<equiv> { I. corona_scenarioO \<rightarrow>\<^sub>i* I }"
fixes corona_KripkeO
defines "corona_KripkeO \<equiv> Kripke corona_statesO IcoronaO"
fixes scoronaO 
defines "scoronaO \<equiv> {x. \<exists> n. \<not> global_policyO'' x (Efid n)}"  
fixes scoronaO' 
defines "scoronaO' \<equiv> {x. \<exists> n. \<not> global_policyO x (Efid n)}"  

begin
(* For the encoding of the efids as powers of primes we need some mathematical facts to 
   provide the foundations to show injectivity results. *)
lemma powers_diff: "n > 0 \<Longrightarrow> x > 1 \<Longrightarrow> (x :: nat)^n < x^(n+1)"
  by (meson less_add_one power_strict_increasing)

lemma prime_powers_diff0: "(m :: nat) > 0 \<Longrightarrow> (n:: nat) > 0 \<Longrightarrow> (p::nat) > 1 \<Longrightarrow> (q:: nat)> 1 \<Longrightarrow> 
                          coprime p q \<Longrightarrow> p^n = q^m \<Longrightarrow> p = q"
  by (metis One_nat_def coprime_1_right coprime_crossproduct_nat coprime_power_left_iff less_numeral_extra(4) one_less_power power_0 power_Suc power_one_right)

lemma prime_powers_diff: "(m :: nat) > 0 \<Longrightarrow> (n:: nat) > 0 \<Longrightarrow> (p::nat) > 1 \<Longrightarrow> (q:: nat)> 1 \<Longrightarrow> 
                          coprime p q \<Longrightarrow> p \<noteq> q \<Longrightarrow> p^n \<noteq> q^m" 
  apply (erule contrapos_nn)
  by (erule prime_powers_diff0)

lemma Efid_eq: "n \<noteq> m \<Longrightarrow> Efid n \<noteq> Efid m"
  by simp

definition prime:: "nat \<Rightarrow> bool"
  where
  "prime p \<equiv> 1 < p \<and> (\<forall> x:: nat. x dvd p \<longrightarrow> x = 1 \<or> x = p)"

lemma primeI: "1 < p \<Longrightarrow> (\<forall> x:: nat. x dvd p \<longrightarrow> x = 1 \<or> x = p) \<Longrightarrow> prime p"
  by (unfold prime_def, simp)

lemma prime_coprime: "p \<noteq> q \<Longrightarrow> prime p \<Longrightarrow> prime q \<Longrightarrow> coprime p q"
  by (metis nat_dvd_1_iff_1 not_coprimeE scenarioCoronaOne.prime_def)

lemma dvd_imp_le: "0 < (n :: nat) \<Longrightarrow> (q :: nat) dvd n \<Longrightarrow> q \<le> n"
  by (rule Nat.dvd_imp_le)

lemma not_prime_div_primeOO: "\<forall> (n :: nat) > 1. (\<exists> (q :: nat). q dvd n)"
  by blast 

lemma not_prime_div_primeO: "\<forall> (n :: nat) > 1. prime n \<or> (\<exists> (q :: nat) < n. prime q \<and> q dvd n)" 
  apply (rule allI)
  apply (rule nat_less_induct)
  by (metis dvd_pos_nat gcd_nat.strict_trans less_trans nat_dvd_not_less nat_neq_iff one_dvd scenarioCoronaOne.primeI zero_less_one)

lemma not_prime_div_prime[rule_format]: "\<forall> (n :: nat) > 1. \<not>(prime n) \<longrightarrow> (\<exists> (q :: nat) < n. prime q \<and> q dvd n)"
 by (insert not_prime_div_primeO, blast)

(* need a simplifying lemma to enhance prime number checking*)
lemma prime_check_upto_squareroot: "1 < x \<Longrightarrow> (\<And> (q:: nat). q^2 \<le> x \<Longrightarrow> prime q \<Longrightarrow> \<not>(q dvd x)) \<Longrightarrow> prime x"
  apply (rule primeI, assumption)
  apply (rule allI, rule impI)
  apply (subgoal_tac "~(1 < xa \<and> xa < x)")
   apply (metis One_nat_def Suc_leI dvdE dvd_imp_le le_neq_implies_less mult_eq_0_iff neq0_conv not_less_zero)
  apply (rule notI)
  apply (erule conjE)
  apply (case_tac "xa^2 \<le> x")
(* *)
   apply (case_tac "prime xa")
    apply simp
   apply (frule_tac n = xa in not_prime_div_prime, assumption)
   apply (erule exE, erule conjE, erule conjE)
   apply (subgoal_tac "q dvd x",simp)
    apply (subgoal_tac "q^2 \<le> x",simp)
  apply (meson le_trans nat_le_linear not_less power2_nat_le_eq_le)
  apply (erule dvd_trans,assumption)
(* *)
  apply (subgoal_tac "? xb. xa * xb = x \<and> xb^2 \<le> x")
   prefer 2
   apply (subgoal_tac "\<exists> k. x = xa * k")
    prefer 2
    apply force
   apply (erule exE)
   apply (rule_tac x = k in exI)
  apply (rule conjI, erule sym)
   apply (subgoal_tac "(xa * k)^2 > x")
    apply (subgoal_tac "xa^2 > x")
     prefer 2
  apply simp
    apply (metis mult.commute mult_le_mono1 nat_le_linear power2_eq_square)
   apply (metis nat_1_add_1 power_one_right scenarioCoronaOne.powers_diff zero_less_one)
  apply (erule exE)
  apply (erule conjE)
  apply (subgoal_tac "xb dvd x")
   prefer 2
  apply force
(* same proof as before *)
   apply (case_tac "prime xb")
   apply simp
  apply (subgoal_tac "1 < xb")
   prefer 2
  apply (simp add: prime_def, force)
   apply (frule_tac n = xb in not_prime_div_prime, assumption)
   apply (erule exE, erule conjE, erule conjE)
   apply (subgoal_tac "q dvd x",simp)
    apply (subgoal_tac "q^2 \<le> x",simp)
  apply (meson le_trans nat_le_linear not_less power2_nat_le_eq_le)
by (erule dvd_trans,assumption)


lemma prime_2: "prime 2"
  by (metis One_nat_def Suc_leI lessI not_less numeral_2_eq_2 scenarioCoronaOne.not_prime_div_prime scenarioCoronaOne.prime_def)
(*
  apply (rule prime_check_upto_squareroot)
   apply simp
  by (metis One_nat_def Suc_leI add_Suc_right less_irrefl less_le_trans nat_arith.rule0 numeral_2_eq_2 power2_eq_square power_one_right scenarioCoronaOne.powers_diff scenarioCoronaOne.prime_def zero_less_Suc)
*)
(*
  by (smt (verit, ccfv_SIG) dvdE dvd_antisym dvd_triv_right even_mult_iff mult.commute mult_2 mult_cancel_left nat.simps(3) nat_1_add_1 numerals(2) scenarioCoronaOne.prime_def)
*)
  
lemma prime_3: "prime 3"
  by (metis (no_types, lifting) Nat.dvd_imp_le One_nat_def Suc_leI antisym le_neq_implies_less less_add_same_cancel2 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit1 numerals(1) odd_numeral one_add_one prime_check_upto_squareroot scenarioCoronaOne.prime_def zero_less_Suc)


lemma prime_5: "prime 5"
  apply (rule prime_check_upto_squareroot)
   apply simp
  apply (subgoal_tac "q = 2 \<or> q = 3")
  using Groups.add_ac(2) apply auto[1]
  apply (simp add: prime_def)
  by (smt (z3) Groups.add_ac(2) One_nat_def Suc_leI add_Suc_right add_le_cancel_left add_left_cancel le_less_trans mult.commute mult_2 n_less_n_mult_m nat.simps(1) nat_arith.rule0 nat_le_linear nat_neq_iff not_less numeral.simps(2) numeral.simps(3) power2_eq_square times_nat.simps(2) zero_less_one)

lemma prime_7: "prime 7"
  apply (rule prime_check_upto_squareroot)
   apply simp
  apply (subgoal_tac "q = 2")
  apply (smt (z3) Groups.add_ac(2) Suc3_eq_add_3 Suc_eq_numeral less_add_same_cancel2 mult.commute mult_2 mult_Suc_right not_less numeral.simps(2) numeral.simps(3) numeral_3_eq_3 numeral_nat(1) odd_numeral plus_nat.simps(2) power2_eq_square zero_less_Suc)
  apply (simp add: prime_def)
  by (smt (z3) Suc3_eq_add_3 Suc_leI add_mono_thms_linordered_semiring(1) le_less_trans le_neq_implies_less less_Suc_eq mult_Suc_right n_less_m_mult_n nat.simps(1) not_le numeral.simps(3) numeral_2_eq_2 numeral_3_eq_3 numeral_nat(1) plus_nat.simps(2) power2_eq_square)

lemma prime_11: "prime 11"
  apply (rule prime_check_upto_squareroot)
   apply simp
  apply (subgoal_tac "q = 2 \<or> q = 3")
  using Groups.add_ac(2) apply auto[1]
  apply (simp add: prime_def)
  by (smt (z3) Groups.add_ac(2) One_nat_def Suc_leI add_Suc_right add_le_cancel_left add_left_cancel le_less_trans mult.commute mult_2 n_less_n_mult_m nat.simps(1) nat_arith.rule0 nat_le_linear nat_neq_iff not_less numeral.simps(2) numeral.simps(3) power2_eq_square times_nat.simps(2) zero_less_one)

lemma prime_13: "prime 13"
  apply (rule prime_check_upto_squareroot)
   apply simp
  apply (subgoal_tac "q = 2 \<or> q = 3")
  using Groups.add_ac(2) apply auto[1]
  apply (simp add: prime_def)
  by (smt (z3) Groups.add_ac(2) One_nat_def Suc_leI add_Suc_right add_le_cancel_left add_left_cancel le_less_trans mult.commute mult_2 n_less_n_mult_m nat.simps(1) nat_arith.rule0 nat_le_linear nat_neq_iff not_less numeral.simps(2) numeral.simps(3) power2_eq_square times_nat.simps(2) zero_less_one)


lemma square_le: "(n :: nat) \<le> m \<Longrightarrow> n^2 \<le> m^2"
  using power2_nat_le_eq_le by blast

lemma five_sq: "(5 :: nat)\<^sup>2 = (25 :: nat)"
  by auto

lemma fivelem: "(5 :: nat) \<le> (q :: nat) \<Longrightarrow> (25 :: nat) \<le> (q :: nat)^2" 
  apply (subgoal_tac "(5 :: nat)^2 = 25")
   apply (metis scenarioCoronaOne.square_le)
by (rule five_sq)

lemma q4_gr: "(q :: nat) > 4 \<Longrightarrow> q^2 > 17"
  apply (subgoal_tac "5 \<le> (q :: nat)")
  prefer 2
   apply simp
  apply (subgoal_tac "(25 :: nat) \<le> (q :: nat)^2")
  apply linarith
  using scenarioCoronaOne.fivelem by auto

lemma prime_17: "prime 17"
  apply (rule prime_check_upto_squareroot)
   apply simp
  apply (subgoal_tac "q = 2 \<or> q = 3")
  using Groups.add_ac(2) apply auto[1]
  apply (subgoal_tac "q \<le> 4")
  apply (simp add: prime_def)
  apply (metis Suc_leI add_Suc_right antisym even_numeral le_neq_implies_less nat_arith.rule0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0)
  by (meson not_le scenarioCoronaOne.q4_gr)

lemma coprime_sym: "coprime a b \<Longrightarrow> coprime b a"
  by (rule Rings.algebraic_semidom_class.coprime_imp_coprime)

(* coprime lemmas for the first few primes *)
lemma coprime_2_3: "coprime (2:: nat) 3"
  apply  (rule prime_coprime)
    apply simp
  apply (rule prime_2)
  by (rule prime_3)

lemma coprime_3_2: "coprime (3::nat) 2"
  by (rule coprime_sym, rule coprime_2_3)

lemma coprime_2_13: "coprime (2 :: nat) 13"
  apply  (rule prime_coprime)
    apply simp
  apply (rule prime_2)
  by (rule prime_13)

lemma coprime_13_2: "coprime (13:: nat) 2"
  by (rule coprime_sym, rule coprime_2_13)

lemma coprime_3_13: "coprime (3:: nat) 13"
  apply  (rule prime_coprime)
    apply simp
  apply (rule prime_3)
  by (rule prime_13)

lemma coprime_13_3: "coprime (13::nat) 3"
  by (rule coprime_sym, rule coprime_3_13)

lemma coprime_5_2: "coprime (5 :: nat) 2"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_5)
  by (rule prime_2)

lemma coprime_2_5: "coprime (2 :: nat) 5"
  by (rule coprime_sym, rule coprime_5_2)

lemma coprime_5_3: "coprime (5 :: nat) 3"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_5)
  by (rule prime_3)

lemma coprime_3_5: "coprime 3 (5 :: nat)"
  by (rule coprime_sym, rule coprime_5_3)

lemma coprime_5_11: "coprime (5:: nat) 11"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_5)
  by (rule prime_11)

lemma coprime_5_13: "coprime (5:: nat) 13"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_5)
  by (rule prime_13)

lemma coprime_13_5: "coprime (13:: nat) 5"
  by (rule coprime_sym, rule coprime_5_13)

lemma coprime_7_2: "coprime (7 :: nat)(2 :: nat)"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_7)
  by (rule prime_2)

lemma coprime_2_7: "coprime (2 :: nat) 7"
  by (rule coprime_sym, rule coprime_7_2)

lemma coprime_7_3: "coprime (7 :: nat)(3 :: nat)"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_7)
  by (rule prime_3)

lemma coprime_3_7: "coprime (3 :: nat) 7"
  by (rule coprime_sym, rule coprime_7_3)


lemma coprime_7_5: "coprime (7 :: nat)(5 :: nat)"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_7)
  by (rule prime_5)

lemma coprime_5_7: "coprime (5::nat)(7::nat)"
  by (rule coprime_sym, rule coprime_7_5)

lemma coprime_7_13: "coprime (7 :: nat)(13 :: nat)"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_7)
  by (rule prime_13)

lemma coprime_13_7: "coprime (13:: nat) 7"
  by (rule coprime_sym, rule coprime_7_13)

lemma coprime_11_7: "coprime (11 :: nat) (7:: nat)"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_11)
  by (rule prime_7)

lemma coprime_7_11: "coprime (7:: nat) 11"
  by (rule coprime_sym, rule coprime_11_7)


lemma coprime_11_5: "coprime (11 :: nat) 5"
  apply (rule prime_coprime)
    apply simp
  apply (rule prime_11)
  by (rule prime_5)

lemma coprime_11_3: "coprime (11 :: nat)(3::nat)"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_11)
  by (rule prime_3)

lemma coprime_3_11: "coprime (3 :: nat) 11"
  by (rule coprime_sym, rule coprime_11_3)

lemma coprime_11_2: "coprime (11:: nat)(2::nat)"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_11)
  by (rule prime_2)

lemma coprime_2_11: "coprime (2 :: nat) 11"
  by (rule coprime_sym, rule coprime_11_2)

lemma coprime_11_13: "coprime (11 :: nat) 13"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_11)
  by (rule prime_13)

lemma coprime_13_11: "coprime (13:: nat) 11"
  by (rule coprime_sym, rule coprime_11_13)

lemma coprime_2_17: "coprime (2:: nat) 17"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_2)
  by (rule prime_17)

lemma coprime_17_2: "coprime (17:: nat) 2"
  by (rule coprime_sym, rule coprime_2_17)

lemma coprime_3_17: "coprime (3:: nat) 17"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_3)
  by (rule prime_17)

lemma coprime_17_3: "coprime (17:: nat) 3"
  by (rule coprime_sym, rule coprime_3_17)

lemma coprime_5_17: "coprime (5:: nat) 17"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_5)
  by (rule prime_17)

lemma coprime_17_5: "coprime (17:: nat) 5"
  by (rule coprime_sym, rule coprime_5_17)

lemma coprime_7_17: "coprime (7:: nat) 17"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_7)
  by (rule prime_17)

lemma coprime_17_7: "coprime (17:: nat) 7"
  by (rule coprime_sym, rule coprime_7_17)

lemma coprime_11_17: "coprime (11:: nat) 17"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_11)
  by (rule prime_17)

lemma coprime_17_11: "coprime (17:: nat) 11"
  by (rule coprime_sym, rule coprime_11_17)

lemma coprime_13_17: "coprime (13:: nat) 17"
  apply (rule prime_coprime)
    apply arith
  apply (rule prime_13)
  by (rule prime_17)

lemma coprime_17_13: "coprime (17:: nat) 13"
  by (rule coprime_sym, rule coprime_13_17)




lemma coprime_range_disjointO: 
"coprime p q \<Longrightarrow> 1 < p \<Longrightarrow> 1 < q \<Longrightarrow> \<exists>z. z \<in> range (\<lambda>x. Efid (p ^ (x + 1))) \<and> z \<in> range (\<lambda>x. Efid (q ^ (x + 1))) \<Longrightarrow> False"
  apply (erule exE, erule conjE, erule rangeE, erule rangeE)
  apply (subgoal_tac "Efid (p ^ (x + 1)) \<noteq>  Efid (q ^ (xa + 1))")
   apply (erule notE, simp)
  apply (rule Efid_eq)
  apply (rule prime_powers_diff)
  apply simp+
  by (metis coprime_Suc_0_right coprime_crossproduct_nat less_not_refl3 mult.commute)


lemma coprime_range_disjoint: 
  assumes "coprime (p :: nat) (q :: nat)" and "1 < p" and "1 < q"
  shows "range (\<lambda>(x :: nat). Efid (p ^ (x + 1))) \<inter> range (\<lambda>x. Efid (q  ^ (x + 1))) = {}"
proof -
  have a: "coprime (p :: nat) (q :: nat) \<Longrightarrow> 1 < p \<Longrightarrow> 1 < q \<Longrightarrow>
                   (\<exists> z. z \<in> range (\<lambda>(x :: nat). Efid (p ^ (x + 1))) \<and> z \<in> range (\<lambda>x. Efid (q  ^ (x + 1))))
                    \<Longrightarrow> False" 
  proof - 
    show "coprime p q \<Longrightarrow>
    1 < p \<Longrightarrow> 1 < q \<Longrightarrow> \<exists>z. z \<in> range (\<lambda>x. Efid (p ^ (x + 1))) \<and> z \<in> range (\<lambda>x. Efid (q ^ (x + 1))) \<Longrightarrow> False "
      by (rule coprime_range_disjointO)
  qed
    then have "coprime (p :: nat) (q :: nat) \<Longrightarrow> 1 < p \<Longrightarrow> 1 < q \<Longrightarrow>
                   \<not>(\<exists> z. z \<in> range (\<lambda>(x :: nat). Efid (p ^ (x + 1))) \<and> z \<in> range (\<lambda>x. Efid (q  ^ (x + 1))))" 
    by (rule notI) 
  from this and assms show ?thesis by auto
qed

lemma coprime_range_disjointOO: 
  "coprime (p :: nat) (q :: nat) \<Longrightarrow> 1 < p \<Longrightarrow>1 < q \<Longrightarrow>
  range (\<lambda>(x :: nat). Efid (p * p ^ x)) \<inter> range (\<lambda>x. Efid (q * q ^ x)) = {}"
  by (drule coprime_range_disjoint, assumption+, simp)


(* actor invariants for example *)
lemma all_actors: "actors_graph(graphI corona_scenarioO) = corona_actorsO"
proof (simp add: corona_scenarioO_def corona_actorsO_def ex_graphO_def actors_graph_def nodes_def
                 ex_loc_assO_def, rule equalityI)
  show "{x. \<exists>y. (y = shopO \<longrightarrow>
             (shopO = pubO \<longrightarrow> x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'') \<and>
             (shopO \<noteq> pubO \<longrightarrow> x = ''Charly'' \<or> x = ''David'' \<or> x = ''Flo'')) \<and>
            (y \<noteq> shopO \<longrightarrow>
             (y = pubO \<longrightarrow> (\<exists>y. y = shopO \<or> y = pubO \<and> pubO = shopO) \<and> (x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'')) \<and>
             y = pubO)}
    \<subseteq> {''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}"
    by auto
next show "{''Alice'', ''Bob'', ''Charly'', ''David'', ''Eve'', ''Flo''}
    \<subseteq> {x. \<exists>y. (y = shopO \<longrightarrow>
                (shopO = pubO \<longrightarrow> x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'') \<and>
                (shopO \<noteq> pubO \<longrightarrow> x = ''Charly'' \<or> x = ''David'' \<or> x = ''Flo'')) \<and>
               (y \<noteq> shopO \<longrightarrow>
                (y = pubO \<longrightarrow> (\<exists>y. y = shopO \<or> y = pubO \<and> pubO = shopO) \<and> (x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''Eve'')) \<and>
                y = pubO)}"
    using pubO_def shopO_def by auto
qed

lemma all_corona_actors: "(corona_scenarioO, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI y) = corona_actorsO"
  using all_actors same_actors by auto

(* nodes invariants *)
lemma same_nodes: "(corona_scenarioO, s) \<in> {(x::InfrastructureOne.infrastructure, y::InfrastructureOne.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> InfrastructureOne.nodes (graphI corona_scenarioO) = InfrastructureOne.nodes (graphI s)"
by (erule same_nodes)

(* efids invariants *)

lemma isthere_lem00: " a \<in>  agra (graphI corona_scenarioO) l \<Longrightarrow> l \<in> nodes (graphI corona_scenarioO) \<Longrightarrow>
            efids_cur (cgra (graphI corona_scenarioO) a) \<in> egra (graphI corona_scenarioO) l"
  apply (simp add: corona_scenarioO_def ex_graphO_def ex_loc_assO_def nodes_def ex_credsO_def ex_efidsO_def
             shopO_def pubO_def)
  by (smt One_nat_def char.inject insertE list.inject location.inject mem_Collect_eq n_not_Suc_n shopO_def singleton_conv)

lemma isthere_lem': "(corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in>  agra (graphI s) l  \<Longrightarrow>
efids_cur (InfrastructureOne.cgra (graphI s) a) \<in> egra (graphI s) l"
  apply (erule rtrancl_induct)
  oops

lemma efids_root_lem: "a \<in> actors_graph (InfrastructureOne.graphI corona_scenarioO) \<Longrightarrow> 
                      a' \<in> actors_graph (InfrastructureOne.graphI corona_scenarioO) \<Longrightarrow>
                 a \<noteq> a' \<Longrightarrow>
                  efids_root (cgra (InfrastructureOne.graphI corona_scenarioO) a) \<noteq> 
                  efids_root (cgra (InfrastructureOne.graphI corona_scenarioO) a')"
    apply (simp add: rmapO_def ref_map_def move_graph_a_def  corona_scenarioO_def Infrastructure.move_graph_a_def)
  apply (simp add: repl_efr_def ex_graphO_def ex_credsO_def)
  by (smt CollectD InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps InfrastructureOne.gra.simps InfrastructureOne.nodes_def ex_loc_assO_def insertE prod.inject singletonD)


lemma efids_root_minus: "(corona_scenarioO, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
      \<Longrightarrow> a \<in> InfrastructureOne.agra (InfrastructureOne.graphI I) l 
      \<Longrightarrow> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI I)  \<Longrightarrow>
(\<lambda>x. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) x)) `
       (InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a}) =
       (\<lambda>a. efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)) `
       InfrastructureOne.agra (InfrastructureOne.graphI I) l -
       {efids_root (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)}"
  apply auto
  apply (frule eroots_inj_on_inv)
  using efids_root_lem inj_on_def apply blast
  by (metis (mono_tags, lifting) InfrastructureOne.actors_graph_def inj_on_def mem_Collect_eq)


text \<open>Other invariants are that the efids at egra l are in fact efids of the actors at
      that location, i.e. 
       e \<in> egra G l = (\<exists>! a \<in> agra G l.  e \<in> efid_list (cgra G a) (for InfrastructureOne))
                      .....        /\ e = efid_root (cgra G a) 
      
      \<close>
(* We need to develop the starting points for the invariants that are needed to unleash the
   lemma is_there_lem needed in the get case.*)
lemma range_disjoint_corona_scenarioO[rule_format]: "(\<forall> a \<in> actors_graph (InfrastructureOne.graphI corona_scenarioO). 
   (\<forall> a' \<in> actors_graph(InfrastructureOne.graphI corona_scenarioO). a \<noteq> a' \<longrightarrow>
     ((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI corona_scenarioO) a)) \<inter> 
      (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI corona_scenarioO) a')))) = {})))"
proof (unfold corona_scenarioO_def ex_graphO_def ex_credsO_def, simp)
  show "\<forall>a\<in>InfrastructureOne.actors_graph
         (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
           (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                     else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                          else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                               else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                    else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                         else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
           ex_locsO ex_efidsO ex_knosO).
       (a = ''Flo'' \<longrightarrow>
        (\<forall>a'\<in>InfrastructureOne.actors_graph
               (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                 (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                      else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                           else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                     else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                          else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                               else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                 ex_locsO ex_efidsO ex_knosO).
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
         (\<forall>a'\<in>InfrastructureOne.actors_graph
                (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                  (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                       else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                            else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                 else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                      else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                           else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                  ex_locsO ex_efidsO ex_knosO).
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
          (\<forall>a'\<in>InfrastructureOne.actors_graph
                 (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                   (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                        else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                             else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                  else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                       else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                            else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                 else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                   ex_locsO ex_efidsO ex_knosO).
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
           (\<forall>a'\<in>InfrastructureOne.actors_graph
                  (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                    (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                         else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                              else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                   else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                        else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                             else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                  else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                    ex_locsO ex_efidsO ex_knosO).
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
            (\<forall>a'\<in>InfrastructureOne.actors_graph
                   (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                     (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                          else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                               else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                    else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                         else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                              else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                   else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                     ex_locsO ex_efidsO ex_knosO).
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
             (\<forall>a'\<in>InfrastructureOne.actors_graph
                    (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                      (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                           else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                                else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                     else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                          else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                               else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                    else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                      ex_locsO ex_efidsO ex_knosO).
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
             (\<forall>a'\<in>InfrastructureOne.actors_graph
                    (InfrastructureOne.igraph.Lgraph {(pubO, shopO)} ex_loc_assO
                      (\<lambda>x. if x = ''Alice'' then Efids (Efid 1) 0 (\<lambda>n. Efid (2 ^ (n + 1)))
                           else if x = ''Bob'' then Efids (Efid 2) 0 (\<lambda>n. Efid (3 ^ (n + 1)))
                                else if x = ''Charly'' then Efids (Efid 3) 0 (\<lambda>n. Efid (5 ^ (n + 1)))
                                     else if x = ''David'' then Efids (Efid 4) 0 (\<lambda>n. Efid (7 ^ (n + 1)))
                                          else if x = ''Eve'' then Efids (Efid 5) 0 (\<lambda>n. Efid (11 ^ (n + 1)))
                                               else if x = ''Flo'' then Efids (Efid 6) 0 (\<lambda>n. Efid (13 ^ (n + 1)))
                                                    else Efids (Efid 0) 0 (\<lambda>n. Efid (17 ^ (n + 1))))
                      ex_locsO ex_efidsO ex_knosO).
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
    by (smt (z3) InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps all_not_in_conv ex_loc_assO_def insertE mem_Collect_eq)
qed

lemma inj_on_corona_scenarioO: "inj_on (\<lambda>x. efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI corona_scenarioO) x))
        (InfrastructureOne.actors_graph (InfrastructureOne.graphI corona_scenarioO))"
  by (simp add: corona_scenarioO_def inj_on_def ex_graphO_def ex_knosO_def pubO_def shopO_def
                   ex_loc_assO_def ex_credsO_def ex_locsO_def ex_efidsO_def actors_graph_def)
 

lemma l_eq_corona_scenarioO[rule_format]: "(\<forall> l l'. l \<in> nodes (graphI corona_scenarioO) \<longrightarrow>
                a \<in>  agra (graphI corona_scenarioO) l \<longrightarrow>  a \<in>  agra (graphI corona_scenarioO) l' \<longrightarrow> l = l')"
  by (simp add: corona_scenarioO_def ex_graphO_def ex_loc_assO_def nodes_def)

lemma coronaO_efids_list_inj: 
"a \<in> actors_graph(InfrastructureOne.graphI corona_scenarioO) \<Longrightarrow> 
inj (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI corona_scenarioO) a))"
  sorry

lemma efid_in_range_corona_scenarioO: "(\<forall> l \<in> nodes (graphI corona_scenarioO).
         (\<forall> e \<in> (egra (InfrastructureOne.graphI corona_scenarioO) l).
         (\<exists> a \<in> actors_graph (graphI corona_scenarioO). 
             e \<in> range (efids_list (InfrastructureOne.cgra (graphI corona_scenarioO) a)))))"
  sorry


lemma efid_kgra_in_range_corona_scenarioO: "(\<forall> l \<in> InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO). 
         (\<forall> h \<in> InfrastructureOne.actors_graph(InfrastructureOne.graphI corona_scenarioO).
         (\<forall> e \<in> (snd`((InfrastructureOne.kgra (InfrastructureOne.graphI corona_scenarioO) h l))).
         (\<exists> a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI corona_scenarioO). 
           e \<in> range (InfrastructureOne.efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI corona_scenarioO) a))))))"
  sorry

lemma efid_eq_efid_cur_corona_scenarioO: "lb \<in> InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI corona_scenarioO) lb \<Longrightarrow>
       \<exists>a\<in>InfrastructureOne.agra (InfrastructureOne.graphI corona_scenarioO) lb.
          e = efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI corona_scenarioO) a)"
  sorry

lemma anonymous_actor_corona_scenarioO: " lb \<in> InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) \<Longrightarrow>
       e \<in> InfrastructureOne.egra (InfrastructureOne.graphI corona_scenarioO) lb \<Longrightarrow>
       anonymous_actor corona_scenarioO e \<in> InfrastructureOne.agra (InfrastructureOne.graphI corona_scenarioO) lb"
  sorry

lemma refmapOne_lem: "\<forall>s::InfrastructureOne.infrastructure.
       (corona_scenarioO, s) \<in> {(x::InfrastructureOne.infrastructure, y::InfrastructureOne.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>s'::InfrastructureOne.infrastructure. s \<rightarrow>\<^sub>n s' \<longrightarrow> rmapO s \<rightarrow>\<^sub>n rmapO s')"
proof (clarify, frule same_nodes, frule init_state_policy, erule state_transition_in.cases)
  show "\<And>s s' G I a l l' I'.
       (corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) =
       InfrastructureOne.nodes (InfrastructureOne.graphI s) \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       l' \<in> InfrastructureOne.nodes G \<Longrightarrow>
       a \<in> InfrastructureOne.actors_graph (InfrastructureOne.graphI I) \<Longrightarrow>
       InfrastructureOne.enables I l' (Actor a) move \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.move_graph_a a l l' (InfrastructureOne.graphI I))
        (InfrastructureOne.delta I) \<Longrightarrow>
       rmapO s \<rightarrow>\<^sub>n rmapO s'"
    apply (subgoal_tac "(\<forall> a \<in> actors_graph (InfrastructureOne.graphI s). 
(\<forall> a' \<in> actors_graph(InfrastructureOne.graphI s). a \<noteq> a' \<longrightarrow>
((range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI s) a)) \<inter> 
 (range (efids_list (InfrastructureOne.cgra (InfrastructureOne.graphI s) a')))) = {})))")
    prefer 2
     apply (simp add: ran_efids_list_disjoint_refl range_disjoint_corona_scenarioO)
  apply (rule_tac I = "rmapO s" and I' = "rmapO s'" and l = l and l' = l' 
                             and a = a 
 in Infrastructure.state_transition_in.move)
  apply (rule refl)
         apply (simp add: rmapO_def ref_map_def atI_def Infrastructure.atI_def)
         apply (simp add: rmapO_def ref_map_def nodes_def Infrastructure.nodes_def)
         apply (simp add: rmapO_def ref_map_def nodes_def Infrastructure.nodes_def)
      apply (simp add: rmapO_def ref_map_def actors_graph_def Infrastructure.actors_graph_def)
    apply (simp add: Infrastructure.nodes_def InfrastructureOne.nodes_def)
      apply (simp add: nodes_def Infrastructure.nodes_def atI_def rmapO_def local_policies_def)
(* *)
     apply (simp add: rmapO_def ref_map_def enables_def Infrastructure.enables_def)
     apply (erule bexE)
    apply (case_tac x, simp, erule conjE)
  apply (rule_tac x = x in bexI, simp)
     apply(simp add: local_policies_def shop_def pub_def atI_def)
    apply (smt InfrastructureOne.delta.simps One_nat_def corona_scenarioO_def empty_iff local_policiesO_def prod.inject pubO_def shopO_def singletonD)
(* *)
    apply (simp add: rmapO_def ref_map_def  corona_scenarioO_def InfrastructureOne.move_graph_a_def
                     Infrastructure.move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
    apply (erule conjE)
     apply (rule conjI)
      apply (rule ext,simp)
    apply (rule conjI)
      apply (rule impI)
      apply (rule conjI)
    apply (rule impI)
       apply simp
      apply (rule impI)
    thm repl_efr_def
      apply (unfold repl_efr_def) 
      apply (simp add: corona_scenarioO_def efids_root_minus)
      apply blast 
    apply (rule ext_ifte)
    apply (smt (z3) Collect_cong Diff_iff InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps InfrastructureOne.gra.simps InfrastructureOne.nodes_def fun_upd_apply insert_iff singletonD)
    apply simp
     apply (rule ext_image)
     apply (rule ballI)
     apply (case_tac x, simp)
(* *)
    apply (subgoal_tac "(anonymous_actor (InfrastructureOne.infrastructure.Infrastructure
              (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                ((InfrastructureOne.agra (InfrastructureOne.graphI I))
                 (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l - {a},
                  l' := insert a (InfrastructureOne.agra (InfrastructureOne.graphI I) l')))
                (InfrastructureOne.cgra (InfrastructureOne.graphI I)) (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                ((InfrastructureOne.egra (InfrastructureOne.graphI I))
                 (l := InfrastructureOne.egra (InfrastructureOne.graphI I) l -
                       {efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a)},
                  l' :=
                    insert (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) a))
                     (InfrastructureOne.egra (InfrastructureOne.graphI I) l')))
                (InfrastructureOne.kgra (InfrastructureOne.graphI I)))
              (InfrastructureOne.delta I))
            b) = (anonymous_actor I b)")
      apply (rotate_tac -1)
    apply (erule ssubst)
      apply (rule refl)
     apply (rule sym)
    apply (rule anonymous_actor_eq)
    using InfrastructureOne.move_graph_a_def InfrastructureOne.state_transition_in.move apply presburger
        apply force
    apply (rule ballI)
       apply (rule efids_list_inj_refl)
    apply simp
    using all_corona_actors corona_scenarioO_def apply blast
    using all_corona_actors coronaO_efids_list_inj corona_scenarioO_def apply blast
      apply blast
     apply simp
    thm efid_kgra_in_range_invariantOO
     apply (rule_tac I = corona_scenarioO in efid_kgra_in_range_invariantOO)
    using corona_scenarioO_def apply presburger
    using efid_in_range_corona_scenarioO apply fastforce
        apply (meson efid_kgra_in_range_corona_scenarioO)
       prefer 3
    apply (subgoal_tac "b \<in> snd ` (InfrastructureOne.kgra (InfrastructureOne.graphI I) aa la)")
        apply simp
    apply (metis image_iff snd_conv)
    apply (erule conjE)
       apply assumption
    apply (erule conjE)
     apply assumption
(* *)
    apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
      apply force
    apply (rule ext_ifte)
      apply force
     apply force
    apply (rule conjI)
     apply (rule impI)+
    apply (rule conjI)
    apply meson
    apply (rule ext_ifte)
    apply force
     apply simp
    apply (rule ext_ifte)
    using InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps InfrastructureOne.gra.simps InfrastructureOne.nodes_def apply presburger
    apply simp
     apply (rule ext_image)
     apply (rule ballI)
     apply (case_tac x, simp)
    apply (subgoal_tac "(anonymous_actor
            (InfrastructureOne.infrastructure.Infrastructure
              (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I))
                (InfrastructureOne.kgra (InfrastructureOne.graphI I)))
              (InfrastructureOne.delta I))
            b) = (anonymous_actor I b)")
      apply (rotate_tac -1)
    apply (erule ssubst)
      apply (rule refl)
     apply (rule sym)
    apply (rule anonymous_actor_eq)
    using InfrastructureOne.move_graph_a_def InfrastructureOne.state_transition_in.move apply presburger
    apply force
    apply (rule ballI)
       apply (rule efids_list_inj_refl)
    apply simp
    using all_corona_actors corona_scenarioO_def apply blast
    using all_corona_actors coronaO_efids_list_inj corona_scenarioO_def apply blast
      apply blast
     apply simp
     apply (rule_tac I = corona_scenarioO in efid_kgra_in_range_invariantOO)
    using corona_scenarioO_def apply presburger
    using efid_in_range_corona_scenarioO apply fastforce
        apply (meson efid_kgra_in_range_corona_scenarioO)
       prefer 3
    apply (subgoal_tac "b \<in> snd ` (InfrastructureOne.kgra (InfrastructureOne.graphI I) aa la)")
        apply simp
    apply (metis image_iff snd_conv)
    apply (erule conjE)
       apply assumption
    apply (erule conjE)
     by assumption
 next show "\<And>s s' G I a l I'.
       (corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) =
       InfrastructureOne.nodes (InfrastructureOne.graphI s) \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (a := (InfrastructureOne.kgra G a)
              (l := {(x, y). x \<in> InfrastructureOne.agra G l \<and> y \<in> InfrastructureOne.egra G l}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       rmapO s \<rightarrow>\<^sub>n rmapO s'"
  proof (rule_tac I = "rmapO s" and I' = "rmapO s'" and l = l  
                             and a = a 
 in Infrastructure.state_transition_in.get, rule refl, simp add: rmapO_def ref_map_def atI_def Infrastructure.atI_def
     ,simp add: rmapO_def ref_map_def nodes_def enables_def Infrastructure.enables_def
              local_policies_def Infrastructure.nodes_def shop_def pub_def)
show "\<And>s s' G I a l I'.
       (corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) =
       InfrastructureOne.nodes (InfrastructureOne.graphI s) \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (a := (InfrastructureOne.kgra G a)
              (l := {(x, y). x \<in> InfrastructureOne.agra G l \<and> y \<in> InfrastructureOne.egra G l}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       Infrastructure.enables (rmapO s) l (Actor a) get"
   proof (simp add: rmapO_def ref_map_def nodes_def enables_def Infrastructure.enables_def
              local_policies_def Infrastructure.nodes_def shop_def pub_def)
     show "\<And>s s' G I a l I'.
       (corona_scenarioO, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       {x. \<exists>y. (x, y) \<in> InfrastructureOne.gra (InfrastructureOne.graphI corona_scenarioO) \<or>
               (y, x) \<in> InfrastructureOne.gra (InfrastructureOne.graphI corona_scenarioO)} =
       {x. \<exists>y. (x, y) \<in> InfrastructureOne.gra (InfrastructureOne.graphI I) \<or>
               (y, x) \<in> InfrastructureOne.gra (InfrastructureOne.graphI I)} \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta I \<Longrightarrow>
       s = I \<Longrightarrow>
       s' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
          (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I))
          (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I))
          ((InfrastructureOne.kgra (InfrastructureOne.graphI I))
           (a := (InfrastructureOne.kgra (InfrastructureOne.graphI I) a)
              (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l \<times>
                    InfrastructureOne.egra (InfrastructureOne.graphI I) l))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureOne.graphI I\<^esub> l \<Longrightarrow>
       \<exists>y. (l, y) \<in> InfrastructureOne.gra (InfrastructureOne.graphI I) \<or>
           (y, l) \<in> InfrastructureOne.gra (InfrastructureOne.graphI I) \<Longrightarrow>
       \<exists>x\<in>InfrastructureOne.delta I (InfrastructureOne.graphI I) l. case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
          (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I))
          (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I))
          ((InfrastructureOne.kgra (InfrastructureOne.graphI I))
           (a := (InfrastructureOne.kgra (InfrastructureOne.graphI I) a)
              (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l \<times>
                    InfrastructureOne.egra (InfrastructureOne.graphI I) l))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       l \<noteq> Location (Suc 0) \<longrightarrow> l = Location 0"
        by (metis InfrastructureOne.delta.simps One_nat_def corona_scenarioO_def empty_iff local_policiesO_def pubO_def shopO_def)
    qed
  next show "\<And>s s' G I a l I'.
       (corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) =
       InfrastructureOne.nodes (InfrastructureOne.graphI s) \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> InfrastructureOne.nodes G \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) get \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure
        (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra G) (InfrastructureOne.agra G) (InfrastructureOne.cgra G)
          (InfrastructureOne.lgra G) (InfrastructureOne.egra G)
          ((InfrastructureOne.kgra G)
           (a := (InfrastructureOne.kgra G a)
              (l := {(x, y). x \<in> InfrastructureOne.agra G l \<and> y \<in> InfrastructureOne.egra G l}))))
        (InfrastructureOne.delta I) \<Longrightarrow>
       rmapO s' =
       Infrastructure.infrastructure.Infrastructure
        (Infrastructure.igraph.Lgraph (Infrastructure.gra (Infrastructure.graphI (rmapO s)))
          (Infrastructure.agra (Infrastructure.graphI (rmapO s))) (Infrastructure.cgra (Infrastructure.graphI (rmapO s)))
          (Infrastructure.lgra (Infrastructure.graphI (rmapO s))) (Infrastructure.egra (Infrastructure.graphI (rmapO s)))
          ((Infrastructure.kgra (Infrastructure.graphI (rmapO s)))
           (a := (Infrastructure.kgra (Infrastructure.graphI (rmapO s)) a)
              (l := {(x, y).
                     x \<in> Infrastructure.agra (Infrastructure.graphI (rmapO s)) l \<and>
                     y \<in> Infrastructure.egra (Infrastructure.graphI (rmapO s)) l}))))
        (Infrastructure.delta (rmapO s)) "
      apply (simp add: rmapO_def ref_map_def)
     apply (rule ext,simp)
      apply (rule conjI)
       apply (rule impI)
    apply (rule ext,simp)
       apply (rule conjI)
        apply (rule impI)+
        apply (rule conjI)
         apply (rule impI)+
         apply (rule conjI)
          apply (rule impI)+
          apply (rule conjI)
      apply (rule impI)+
    apply (simp add: image_def)
           apply (rule equalityI)
            apply (rule subsetI)
      apply (case_tac x)
            apply simp
            apply (erule conjE)+
            apply (erule bexE)
            apply (rotate_tac -1)
      apply (erule ssubst)
      apply (rule_tac x = "(anonymous_actor
               (InfrastructureOne.infrastructure.Infrastructure
                 (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                   (InfrastructureOne.agra (InfrastructureOne.graphI I))
                   (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                   (InfrastructureOne.lgra (InfrastructureOne.graphI I))
                   (InfrastructureOne.egra (InfrastructureOne.graphI I))
                   ((InfrastructureOne.kgra (InfrastructureOne.graphI I))
                    (a := (InfrastructureOne.kgra (InfrastructureOne.graphI I) a)
                       (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l \<times>
                             InfrastructureOne.egra (InfrastructureOne.graphI I) l))))
                 (InfrastructureOne.delta I))
               y)" in bexI)
             apply (rule refl)
      apply (subgoal_tac "anonymous_actor
        (InfrastructureOne.infrastructure.Infrastructure
          (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
            (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I))
            (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I))
            ((InfrastructureOne.kgra (InfrastructureOne.graphI I))
             (a := (InfrastructureOne.kgra (InfrastructureOne.graphI I) a)
                (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l \<times>
                      InfrastructureOne.egra (InfrastructureOne.graphI I) l))))
          (InfrastructureOne.delta I))
        y = anonymous_actor I y")
             apply (rotate_tac -1)
      apply (erule ssubst)
      thm anonymous_actor_invOO
             apply (rule anonymous_actor_invOO)
      apply assumption
      using all_corona_actors apply force
      using coronaO_efids_list_inj apply presburger
      using range_disjoint_corona_scenarioO apply presburger
      using efid_in_range_corona_scenarioO apply fastforce
      using l_eq_corona_scenarioO apply presburger
      using efid_eq_efid_cur_corona_scenarioO apply presburger
      using anonymous_actor_corona_scenarioO apply presburger
              apply blast
      apply assumption
      using InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.get anonymous_actor_def apply fastforce
            apply (rule subsetI)
      apply (case_tac x)
            apply simp
(* *)
           apply (erule conjE)+
           apply (erule bexE)
      apply (rule_tac x = "efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) xa)" in bexI)
            prefer 2
      apply (rule is_there_lem, assumption)
      using range_disjoint_corona_scenarioO apply presburger
      apply (rule inj_on_corona_scenarioO)
      using coronaO_efids_list_inj apply presburger
      using l_eq_corona_scenarioO apply presburger
      using local.isthere_lem00 apply presburger
             apply blast
      apply assumption
(* *)
      apply (rotate_tac -1)
           apply (erule ssubst)
      apply (subgoal_tac "xa = (anonymous_actor
            (InfrastructureOne.infrastructure.Infrastructure
              (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
                (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I))
                (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I))
                ((InfrastructureOne.kgra (InfrastructureOne.graphI I))
                 (a := (InfrastructureOne.kgra (InfrastructureOne.graphI I) a)
                    (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l \<times>
                          InfrastructureOne.egra (InfrastructureOne.graphI I) l))))
              (InfrastructureOne.delta I))
            (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) xa)))")
            apply (rotate_tac -1)
            apply (erule subst, rule refl)
      apply (subgoal_tac "anonymous_actor
        (InfrastructureOne.infrastructure.Infrastructure
          (InfrastructureOne.igraph.Lgraph (InfrastructureOne.gra (InfrastructureOne.graphI I))
            (InfrastructureOne.agra (InfrastructureOne.graphI I)) (InfrastructureOne.cgra (InfrastructureOne.graphI I))
            (InfrastructureOne.lgra (InfrastructureOne.graphI I)) (InfrastructureOne.egra (InfrastructureOne.graphI I))
            ((InfrastructureOne.kgra (InfrastructureOne.graphI I))
             (a := (InfrastructureOne.kgra (InfrastructureOne.graphI I) a)
                (l := InfrastructureOne.agra (InfrastructureOne.graphI I) l \<times>
                      InfrastructureOne.egra (InfrastructureOne.graphI I) l))))
          (InfrastructureOne.delta I))  (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) xa))
         = anonymous_actor I  (efids_cur (InfrastructureOne.cgra (InfrastructureOne.graphI I) xa))")
      apply (rotate_tac -1)
            apply (erule ssubst)
      prefer 2
      using InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps InfrastructureOne.cgra.simps InfrastructureOne.gra.simps InfrastructureOne.graphI.simps InfrastructureOne.nodes_def anonymous_actor_def apply presburger
      apply (rule anonymous_actor_def1b)
      apply (metis empty_iff)
      using all_corona_actors coronaO_efids_list_inj efids_list_inj_refl apply blast
              apply (simp add: ran_efids_list_disjoint_refl range_disjoint_corona_scenarioO)
             apply assumption
            apply (simp)
            apply (rule_tac x = xa in bexI)
             apply (rule efids_cur_in_efids_listO)
             apply (simp add: actors_graph_def, rule_tac x = l in exI, rule conjI, assumption, assumption)+
           apply (rule conjI)
             apply (simp add: actors_graph_def, rule_tac x = l in exI, rule conjI, assumption, assumption)
             apply (rule efids_cur_in_efids_listO)
             apply (simp add: actors_graph_def, rule_tac x = l in exI, rule conjI, assumption, assumption)
(* *)
          apply (rule impI)
      apply (rule ext_image)
          apply (rule ballI)
      using InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.get anonymous_actor_def apply fastforce
         apply (rule impI)+
      apply (rule conjI)
          apply (rule impI)+
      apply simp
      using InfrastructureOne.actors_graph_def InfrastructureOne.atI_def apply force
      apply (simp add: InfrastructureOne.actors_graph_def InfrastructureOne.nodes_def)
      using InfrastructureOne.nodes_def apply fastforce
       apply (rule impI)+
       apply (rule conjI)
        apply (rule impI)+
        apply (rule conjI)
         apply (rule impI)+
      apply (rule conjI)
          apply (rule impI)+
      apply force
      apply (rule impI)
      apply (rule ext_image)
          apply (rule ballI)
      apply (simp add: InfrastructureOne.nodes_def)
      using InfrastructureOne.nodes_def apply force
       apply (rule impI)+
       apply (rule conjI)
        apply (rule impI)+
        apply (rule conjI)
         apply (rule impI)+
      using InfrastructureOne.same_actors0 InfrastructureOne.same_nodes0 InfrastructureOne.state_transition_in.get apply fastforce
      using InfrastructureOne.actors_graph_def InfrastructureOne.nodes_def apply force
      using InfrastructureOne.actors_graph_def InfrastructureOne.atI_def apply force
      apply (rule impI)+
      apply (rule ext_ifte'')
      using InfrastructureOne.actors_graph_def InfrastructureOne.agra.simps InfrastructureOne.gra.simps InfrastructureOne.nodes_def apply presburger
      apply simp
      using InfrastructureOne.same_actors0 InfrastructureOne.state_transition_in.get anonymous_actor_def by fastforce
  qed
next show "\<And>s s' G I a l I'.
       (corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) =
       InfrastructureOne.nodes (InfrastructureOne.graphI s) \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a l G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       rmapO s \<rightarrow>\<^sub>n rmapO s'"
  proof (rule_tac I = "rmapO s" and I' = "rmapO s'" and l = l  
                             and a = a 
 in Infrastructure.state_transition_in.put, rule refl, simp add: rmapO_def ref_map_def atI_def Infrastructure.atI_def
     ,simp add: rmapO_def ref_map_def nodes_def enables_def Infrastructure.enables_def
              local_policies_def Infrastructure.nodes_def shop_def pub_def)
    show "\<And>s s' G I a l I'.
       (corona_scenarioO, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       {x. \<exists>y. (x, y) \<in> InfrastructureOne.gra (InfrastructureOne.graphI corona_scenarioO) \<or>
               (y, x) \<in> InfrastructureOne.gra (InfrastructureOne.graphI corona_scenarioO)} =
       {x. \<exists>y. (x, y) \<in> InfrastructureOne.gra (InfrastructureOne.graphI I) \<or>
               (y, x) \<in> InfrastructureOne.gra (InfrastructureOne.graphI I)} \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta I \<Longrightarrow>
       s = I \<Longrightarrow>
       s' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a l (InfrastructureOne.graphI I))
        (InfrastructureOne.delta I) \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>InfrastructureOne.graphI I\<^esub> l \<Longrightarrow>
       \<exists>x\<in>InfrastructureOne.delta I (InfrastructureOne.graphI I) l. case x of (p, e) \<Rightarrow> put \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a l (InfrastructureOne.graphI I))
        (InfrastructureOne.delta I) \<Longrightarrow>
       l \<noteq> Location (Suc 0) \<longrightarrow> l = Location 0"
      using all_not_in_conv corona_scenarioO_def local_policiesO_def pubO_def shopO_def by fastforce
  next show "\<And>s s' G I a l I'.
       (corona_scenarioO, s) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       InfrastructureOne.nodes (InfrastructureOne.graphI corona_scenarioO) =
       InfrastructureOne.nodes (InfrastructureOne.graphI s) \<Longrightarrow>
       InfrastructureOne.delta corona_scenarioO = InfrastructureOne.delta s \<Longrightarrow>
       s = I \<Longrightarrow>
       s' = I' \<Longrightarrow>
       G = InfrastructureOne.graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       InfrastructureOne.enables I l (Actor a) put \<Longrightarrow>
       I' =
       InfrastructureOne.infrastructure.Infrastructure (InfrastructureOne.put_graph_efid a l G)
        (InfrastructureOne.delta I) \<Longrightarrow>
       rmapO s' =
       Infrastructure.infrastructure.Infrastructure (Infrastructure.put_graph_efid a l (Infrastructure.graphI (rmapO s)))
        (Infrastructure.delta (rmapO s)) "
      apply (simp add: rmapO_def ref_map_def)
    apply (simp add: put_graph_efid_def Infrastructure.put_graph_efid_def)
      apply (rule conjI)
      apply (rule ext, simp)
      using efids_root_efids_inc_lem repl_efr_def apply presburger
      apply (rule conjI)
       apply (rule ext, simp)
       apply (rule conjI)
        apply (rule impI)
      apply (simp add: InfrastructureOne.atI_def efids_root_efids_inc_lem ext_image insert_absorb repl_efr_def)
       apply (rule impI)
      apply (simp add: efids_root_efids_inc_lem ext_image)
      apply (rule ext_ifte)
      apply (metis InfrastructureOne.graphI.simps InfrastructureOne.put_graph_efid_def InfrastructureOne.same_actors0 InfrastructureOne.same_nodes0 InfrastructureOne.state_transition_in.put)
(* *)
      apply (subgoal_tac "InfrastructureOne.kgra
        (InfrastructureOne.graphI
          (InfrastructureOne.infrastructure.Infrastructure
            (InfrastructureOne.put_graph_efid a l (InfrastructureOne.graphI I)) (InfrastructureOne.delta I))) =
          InfrastructureOne.kgra (InfrastructureOne.graphI I)")
       prefer 2
      using InfrastructureOne.graphI.simps InfrastructureOne.kgra.simps InfrastructureOne.put_graph_efid_def apply presburger
       apply (rotate_tac -1)
      apply (erule ssubst)
      apply (rule ext_image)
      apply (rule ballI)
      apply (case_tac x)
      apply simp
      apply (subgoal_tac "(anonymous_actor I b) = (anonymous_actor
                   (InfrastructureOne.infrastructure.Infrastructure
                     (InfrastructureOne.put_graph_efid a l (InfrastructureOne.graphI I)) (InfrastructureOne.delta I))
                   b)")
       prefer 2
      apply (rule anonymous_actor_eq)
      apply (meson InfrastructureOne.state_transition_in.put)
      apply fastforce
      using InfrastructureOne.same_actors coronaO_efids_list_inj efids_list_inj_refl apply blast
        apply (simp add: ran_efids_list_disjoint_refl range_disjoint_corona_scenarioO)
       apply simp
      prefer 2
      using InfrastructureOne.put_graph_efid_def efids_root_efids_inc_lem apply force
(* here *)
      thm efid_kgra_in_range_invariantOO
      apply (rule_tac l = la and h' = aa in efid_kgra_in_range_invariantOO)
      apply assumption
      using efid_in_range_corona_scenarioO apply fastforce
         apply (meson efid_kgra_in_range_corona_scenarioO)
        apply (erule conjE, assumption)+
      by force
  qed
qed


theorem refmapOne: "corona_Kripke \<sqsubseteq>\<^sub>rmapO corona_KripkeO"
proof (rule strong_mt', simp add: corona_KripkeO_def corona_Kripke_def corona_states_def corona_statesO_def state_transition_refl_def, rule conjI)
  show "IcoronaO \<subseteq> {I. (corona_scenarioO, I) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*}"
    using IcoronaO_def by fastforce
next show "Icorona \<subseteq> {I. (corona_scenario, I) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*} \<and>
    rmapO ` IcoronaO \<subseteq> Icorona \<and>
    (\<forall>s. (\<exists>s0\<in>IcoronaO. (s0, s) \<in> {(x, y). x \<rightarrow>\<^sub>i y}\<^sup>*) \<longrightarrow> (\<forall>s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> rmapO s \<rightarrow>\<^sub>i rmapO s')) "
    apply (rule conjI)
    using Icorona_def apply blast
    apply (rule conjI)
     apply (simp add: rmapO_def IcoronaO_def Icorona_def corona_scenarioO_def corona_scenario_def
            ref_map_def ex_graphO_def ex_graph_def pubO_def pub_def shopO_def shop_def ex_loc_ass_def
            ex_loc_assO_def ext ex_credsO_def  ex_creds_def ex_locsO_def ex_locs_def ex_efids_def
            ex_knos_def ex_knosO_def repl_efr_def)
    using IcoronaO_def Infrastructure.state_transition_infra_def InfrastructureOne.state_transition_infra_def refmapOne_lem by auto
qed


lemma step1: "corona_scenarioO  \<rightarrow>\<^sub>n corona_scenarioO'"
proof (rule_tac l = pubO and a = "''Eve''" in get)
  show "graphI corona_scenarioO = graphI corona_scenarioO" by (rule refl)
next show "''Eve'' @\<^bsub>graphI corona_scenarioO\<^esub> pubO" 
    by (simp add: corona_scenarioO_def ex_graphO_def ex_loc_assO_def atI_def nodes_def)
next show "enables corona_scenarioO pubO (Actor ''Eve'') get"
    by (simp add: enables_def corona_scenarioO_def ex_graphO_def local_policiesO_def
                    ex_credsO_def ex_locsO_def)
next show "pubO \<in> nodes (graphI corona_scenarioO)"
    using corona_scenarioO_def ex_graphO_def nodes_def by auto 
next show "corona_scenarioO' =
    Infrastructure
     (Lgraph (gra (graphI corona_scenarioO)) (agra (graphI corona_scenarioO)) (cgra (graphI corona_scenarioO))
       (lgra (graphI corona_scenarioO)) (egra (graphI corona_scenarioO))
       ((kgra (graphI corona_scenarioO))
        (''Eve'' := (kgra (graphI corona_scenarioO) (''Eve''))
           (pubO := {(x, y). x \<in> agra (graphI corona_scenarioO) pubO \<and> y \<in> egra (graphI corona_scenarioO) pubO}))))
     (delta corona_scenarioO)"
    apply (simp add: corona_scenarioO'_def ex_graphO'_def move_graph_a_def 
                     corona_scenarioO_def ex_graphO_def pubO_def shopO_def 
                     ex_loc_assO'_def ex_loc_assO_def ex_efidsO'_def ex_efidsO_def 
                     ex_knosO_def ex_knosO'_def ex_credsO_def)
    apply (rule ext, simp add: insert_Diff_if shopO_def pubO_def)
      apply (rule impI, rule ext)
by auto[1]
qed


lemma step1r: "corona_scenarioO  \<rightarrow>\<^sub>n* corona_scenarioO'"
proof (simp add: state_transition_in_refl_def)
  show " (corona_scenarioO, corona_scenarioO') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  by (insert step1, auto)
qed

lemma step2: "corona_scenarioO'  \<rightarrow>\<^sub>n corona_scenarioO''"
proof (rule_tac l' = shopO and l = pubO and a = "''Bob''" in move, rule refl)
  show "''Bob'' @\<^bsub>graphI corona_scenarioO'\<^esub> pubO"
   by (simp add: corona_scenarioO'_def ex_graphO'_def pubO_def shopO_def atI_def ex_loc_assO_def)
next show "pubO \<in> nodes (graphI corona_scenarioO')"
    by (simp add: corona_scenarioO'_def ex_graphO'_def pubO_def atI_def nodes_def, blast)
next show "shopO \<in> nodes (graphI corona_scenarioO')"
    by (simp add: corona_scenarioO'_def nodes_def ex_graphO'_def, blast)
next show "''Bob'' \<in> actors_graph (graphI corona_scenarioO')"
    by (simp add: actors_graph_def corona_scenarioO'_def ex_graphO'_def nodes_def
                     ex_loc_assO_def shopO_def pubO_def, blast)
next show "enables corona_scenarioO' shopO (Actor ''Bob'') move"
    by (simp add: enables_def corona_scenarioO'_def local_policiesO_def)
next show "corona_scenarioO'' =
    Infrastructure (move_graph_a ''Bob'' pubO shopO (graphI corona_scenarioO')) (delta corona_scenarioO')"
    apply (simp add: corona_scenarioO'_def ex_graphO''_def move_graph_a_def corona_scenarioO''_def 
                     ex_graphO'_def ex_loc_assO_def ex_loc_assO'_def shopO_def pubO_def)
    apply (rule conjI)
      apply (rule ext, simp add: insert_Diff_if shopO_def pubO_def)
    apply (simp add: ex_efidsO_def ex_efidsO'_def shopO_def pubO_def ex_credsO_def)
    by (rule ext, simp add: insert_Diff_if shopO_def pubO_def)
qed

lemma step2r: "corona_scenarioO'  \<rightarrow>\<^sub>n* corona_scenarioO''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioO', corona_scenarioO'') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step2, auto)
qed

lemma step3: "corona_scenarioO''  \<rightarrow>\<^sub>n corona_scenarioO'''"
proof (rule_tac l' = shopO and l = pubO and a = "''Eve''" in move, rule refl)
  show "''Eve'' @\<^bsub>graphI corona_scenarioO''\<^esub> pubO"
   by (simp add: corona_scenarioO''_def ex_graphO''_def pubO_def shopO_def atI_def ex_loc_assO'_def)
next show \<open>pubO \<in> nodes (graphI corona_scenarioO'')\<close>
    by (simp add: corona_scenarioO''_def pubO_def ex_graphO''_def nodes_def, blast)
next show \<open>shopO \<in> nodes (graphI corona_scenarioO'')\<close>
    by (simp add: corona_scenarioO''_def pubO_def ex_graphO''_def nodes_def, blast)
next show \<open>''Eve'' \<in> actors_graph (graphI corona_scenarioO'')\<close>
    by (simp add: actors_graph_def corona_scenarioO''_def ex_graphO''_def nodes_def ex_loc_assO'_def 
                  shopO_def pubO_def, blast)
next show \<open>enables corona_scenarioO'' shopO (Actor ''Eve'') move\<close>
    by (simp add: enables_def corona_scenarioO''_def local_policiesO_def)
next show \<open>corona_scenarioO''' =
    Infrastructure (move_graph_a ''Eve'' pubO shopO (graphI corona_scenarioO'')) (delta corona_scenarioO'')\<close>
    apply (simp add: corona_scenarioO'''_def ex_graphO'''_def move_graph_a_def pubO_def shopO_def
                     corona_scenarioO''_def ex_graphO''_def ex_loc_assO''_def ex_loc_assO'_def)
    apply (rule conjI)
     apply (rule ext, simp add: insert_Diff_if shopO_def pubO_def)+
    apply (simp add: ex_efidsO'_def ex_efidsO''_def shopO_def pubO_def ex_credsO_def)
    by (simp add: insert_Diff_if shopO_def pubO_def)
qed

lemma step3r: "corona_scenarioO''  \<rightarrow>\<^sub>n* corona_scenarioO'''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioO'', corona_scenarioO''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step3, auto)
qed

lemma step4: "corona_scenarioO'''  \<rightarrow>\<^sub>n corona_scenarioO''''"
proof (rule_tac l = shopO and a = "''Eve''" in get, rule refl)
  show \<open>''Eve'' @\<^bsub>graphI corona_scenarioO'''\<^esub> shopO\<close>
   by (simp add: corona_scenarioO'''_def ex_graphO'''_def pubO_def shopO_def atI_def ex_loc_assO''_def)
next show \<open>enables corona_scenarioO''' shopO (Actor ''Eve'') get\<close>
    by (simp add: enables_def corona_scenarioO'''_def local_policiesO_def)
next show "shopO \<in> nodes (graphI corona_scenarioO''')"
    using corona_scenarioO'''_def ex_graphO'''_def nodes_def by auto
next show \<open>corona_scenarioO'''' =
    Infrastructure
     (Lgraph (gra (graphI corona_scenarioO''')) (agra (graphI corona_scenarioO''')) (cgra (graphI corona_scenarioO'''))
       (lgra (graphI corona_scenarioO''')) (egra (graphI corona_scenarioO'''))
       ((kgra (graphI corona_scenarioO'''))
        (''Eve'' := (kgra (graphI corona_scenarioO''') (''Eve''))
           (shopO := {(x, y). x \<in> agra (graphI corona_scenarioO''') shopO \<and> y \<in> egra (graphI corona_scenarioO''') shopO}))))
     (delta corona_scenarioO''') \<close>
    apply (simp add: corona_scenarioO'''_def ex_graphO'''_def move_graph_a_def pubO_def shopO_def
                     corona_scenarioO''''_def ex_graphO''''_def ex_loc_assO''_def ex_loc_assO'_def)
     apply (rule ext, simp add: insert_Diff_if shopO_def pubO_def)+
    apply (simp add: ex_efidsO''_def shopO_def pubO_def ex_knosO'_def ex_knosO''_def)
    apply (rule impI, rule ext)
    apply (simp add: insert_Diff_if shopO_def pubO_def)
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

lemma step4r: "corona_scenarioO'''  \<rightarrow>\<^sub>n* corona_scenarioO''''"
proof (simp add: state_transition_in_refl_def)
  show "(corona_scenarioO''', corona_scenarioO'''') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    by (insert step4, auto)
qed

lemma corona_refO: "[\<N>\<^bsub>(IcoronaO,scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup>)"
  by (metis append_Cons append_Nil refI)  

lemma corona_refO': "[\<N>\<^bsub>(IcoronaO,scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO')\<^esup> \<sqsubseteq>
                  ([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO')\<^esup>)"
  by (metis append_Cons append_Nil refI)  

lemma att_coronaO: "\<turnstile>([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup>)"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(IcoronaO, CoronaO')\<^esub>"
    apply (simp add: IcoronaO_def CoronaO'_def att_base)
    using state_transition_infra_def step1 by blast
next show \<open> \<turnstile>[\<N>\<^bsub>(CoronaO', CoronaO'')\<^esub>, \<N>\<^bsub>(CoronaO'', CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''', scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(CoronaO', scoronaO)\<^esup>\<close>
    apply (subst att_and, simp)
    apply (rule conjI)
     apply (simp add: CoronaO'_def CoronaO''_def att_base state_transition_infra_def step2)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: CoronaO''_def CoronaO'''_def att_base state_transition_infra_def step3)
    apply (subst att_and, simp)
    apply (simp add: CoronaO'''_def scoronaO_def att_base state_transition_infra_def step4)
    apply (rule_tac x = "corona_scenarioO''''" in exI)
    apply (rule conjI)
     prefer 2
    apply (rule step4)
     apply (unfold corona_scenarioO''''_def global_policyO''_def)
     apply (unfold global_policyO''_def identifiableO'_def ex_graphO''''_def ex_loc_assO''_def nodes_def is_singleton_def
                  ex_efidsO''_def pubO_def shopO_def ex_credsO_def ex_locsO_def ex_knosO''_def local_policiesO_def)
     apply (rule_tac x = 3 in exI, simp)
     apply (rule conjI)
    apply (rule impI)
     apply (rule_tac x = "''Bob''" in exI)
      apply (rule_tac  x = "Efid 3" in exI)
      apply (rule equalityI)
          apply auto[1]
      apply simp
by blast
qed


lemma att_coronaO': "\<turnstile>([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO')\<^esup>)"
proof (subst att_and, simp, rule conjI)
  show " \<turnstile>\<N>\<^bsub>(IcoronaO, CoronaO')\<^esub>"
    apply (simp add: IcoronaO_def CoronaO'_def att_base)
    using state_transition_infra_def step1 by blast
next show \<open> \<turnstile>[\<N>\<^bsub>(CoronaO', CoronaO'')\<^esub>, \<N>\<^bsub>(CoronaO'', CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''', scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(CoronaO', scoronaO')\<^esup>\<close>
    apply (subst att_and, simp)
    apply (rule conjI)
     apply (simp add: CoronaO'_def CoronaO''_def att_base state_transition_infra_def step2)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: CoronaO''_def CoronaO'''_def att_base state_transition_infra_def step3)
    apply (subst att_and, simp)
    apply (simp add: CoronaO'''_def scoronaO'_def att_base state_transition_infra_def step4)
    apply (rule_tac x = "corona_scenarioO''''" in exI)
    apply (rule conjI)
     prefer 2
    apply (rule step4)
     apply (unfold corona_scenarioO''''_def global_policyO_def)
     apply (unfold global_policyO_def identifiableO'_def ex_graphO''''_def ex_loc_assO''_def nodes_def is_singleton_def
                  ex_efidsO''_def pubO_def shopO_def ex_credsO_def ex_locsO_def ex_knosO''_def local_policiesO_def)
    apply (rule_tac x = 3 in exI, simp)
    apply (rule set_exI)
     prefer 2
    apply (subgoal_tac 
    "{Location 0, Location 1} \<subseteq> {x. \<exists>y. x = Location 0 \<and> y = Location (Suc 0) \<or> y = Location 0 \<and> x = Location (Suc 0)}")
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
  
lemma corona_abs_attO: "\<turnstile>\<^sub>V([\<N>\<^bsub>(IcoronaO,scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO)\<^esup>)"
   by (rule ref_valI, rule corona_refO, rule att_coronaO)

lemma corona_abs_attO': "\<turnstile>\<^sub>V([\<N>\<^bsub>(IcoronaO,scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO,scoronaO')\<^esup>)"
   by (rule ref_valI, rule corona_refO', rule att_coronaO')


lemma corona_attO: "corona_KripkeO \<turnstile> EF {x. \<exists> n. \<not>(global_policyO'' x (Efid n))}"
proof -
  have a: " \<turnstile>([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO, scoronaO)\<^esup>)"
    by (rule att_coronaO)
  hence "(IcoronaO,scoronaO) = attack ([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO, scoronaO)\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>IcoronaO. i \<rightarrow>\<^sub>i* s} IcoronaO \<turnstile> EF scoronaO"
    using ATV_EF corona_abs_attO by fastforce 
  thus "corona_KripkeO \<turnstile> EF {x::infrastructure.  \<exists> n. \<not> global_policyO'' x (Efid n)}"
    by (simp add: corona_KripkeO_def corona_statesO_def IcoronaO_def scoronaO_def)
qed

lemma corona_attO': "corona_KripkeO \<turnstile> EF {x. \<exists> n. \<not>(global_policyO x (Efid n))}"
proof -
  have a: " \<turnstile>([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO, scoronaO')\<^esup>)"
    by (rule att_coronaO')
  hence "(IcoronaO,scoronaO') = attack ([\<N>\<^bsub>(IcoronaO,CoronaO')\<^esub>, \<N>\<^bsub>(CoronaO',CoronaO'')\<^esub>,  \<N>\<^bsub>(CoronaO'',CoronaO''')\<^esub>, \<N>\<^bsub>(CoronaO''',scoronaO')\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>(IcoronaO, scoronaO')\<^esup>)"
    by simp
  hence "Kripke {s::infrastructure. \<exists>i::infrastructure\<in>IcoronaO. i \<rightarrow>\<^sub>i* s} IcoronaO \<turnstile> EF scoronaO'"
    using ATV_EF corona_abs_attO' by fastforce 
  thus "corona_KripkeO \<turnstile> EF {x::infrastructure.  \<exists> n. \<not> global_policyO x (Efid n)}"
    by (simp add: corona_KripkeO_def corona_statesO_def IcoronaO_def scoronaO'_def)
qed


theorem corona_EFO: "corona_KripkeO \<turnstile> EF scoronaO"
  using corona_attO scoronaO_def by blast 

theorem corona_EFO': "corona_KripkeO \<turnstile> EF scoronaO'"
  using corona_attO' scoronaO'_def by blast 


theorem corona_ATO: "\<exists> A. \<turnstile> A \<and> attack A = (IcoronaO,scoronaO)"
  using att_coronaO attack.simps(2) by blast  

theorem corona_ATO': "\<exists> A. \<turnstile> A \<and> attack A = (IcoronaO,scoronaO')"
  using att_coronaO' attack.simps(2) by blast  

text \<open>Conversely, since we have an attack given by rule @{text \<open>corona_AT\<close>}, we can immediately 
   infer @{text \<open>EF s\<close>} using Correctness @{text \<open>AT_EF\<close>}\footnote{Clearly, this theorem is identical
   to @{text \<open>corona_EF\<close>} and could thus be inferred from that one but we want to show here an 
   alternative way of proving it using the Correctness theorem @{text \<open>AT_EF\<close>}.}.\<close>
theorem corona_EFO'': "corona_KripkeO \<turnstile> EF scoronaO"
  using corona_EFO by auto

theorem corona_EFO''': "corona_KripkeO \<turnstile> EF scoronaO'"
  using corona_EFO' by auto

end
end
