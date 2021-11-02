theory InfrastructureTwo
  imports CoronaAppOne
begin

text \<open>This is the new element for refining the Ephemeral Id -- simply a list
     of ephemeral ids. The cryptographic details can be added here if needed
     but at the current stage of abstraction we are satisfied with t a list.
   The idea is that the current pointer is the first element and that
   the Efids are popped off once used.\<close>
(* datatype efidlist = Efids "efid" "nat" "efid list" *)

primrec efids_root :: "efidlist \<Rightarrow> efid"
  where "efids_root (Efids e n el) = e"
primrec efids_index :: "efidlist \<Rightarrow> nat"
  where "efids_index (Efids e n el) = n"
primrec efids_inc_ind :: "efidlist \<Rightarrow> efidlist"
  where "efids_inc_ind (Efids e n el) = (Efids e (Suc n) el) "
primrec efids_cur:: "efidlist \<Rightarrow> efid"
  where "efids_cur (Efids e n el) = nth el n"
primrec efids_list :: "efidlist \<Rightarrow> efid list"
  where "efids_list (Efids e n el) = el"
definition repl_efr :: "efidlist \<Rightarrow> efid"
  where "repl_efr el \<equiv> efids_root el" 

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                           "identity \<Rightarrow> efidlist"  
                           "location \<Rightarrow> string * (dlm * data) set"
                           "location \<Rightarrow> efid set"
                           "actor \<Rightarrow> location \<Rightarrow> (identity * efid)set"

datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph, location] \<Rightarrow> policy set" 
                       
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l e k) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l e k) = a"
primrec cgra :: "igraph \<Rightarrow> identity \<Rightarrow> efidlist"
where  "cgra(Lgraph g a c l e k) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string * (dlm * data) set)"
  where  "lgra(Lgraph g a c l e k) = l"
primrec egra :: "igraph \<Rightarrow> location \<Rightarrow> efid set"
  where  "egra(Lgraph g a c l e k) = e"
primrec kgra:: "[igraph, actor, location] \<Rightarrow> (identity * efid)set"
  where "kgra(Lgraph g a c l e k) = k"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, identity ] \<Rightarrow> efidlist"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string * (dlm * data)set"
  where "lspace (Infrastructure g d) = lgra g"


(* Functions of the efid datatype that allow to map back uniquely from an efid to its root.
   This is important for the later resolution of close proximities to a covid infected person
   but curiously also for the first refinement map. 
   Depending on whether we chuck out the efids form a location in egra after an actor leaves
   (implementation decision) we could also only consider all the actors that are actually in a 
   location, However, for simplicity we currently consider all actor of the graph when we map back
   over all the efids in a location to gather the efid_roots. Similarly, we have not yet implemented
   an overarching ...
*)
(*
definition efid_to_root ::  "[igraph, efid, identity] \<Rightarrow> efid option"
  where "efid_to_root g e a = 
        (if  e \<in> (set (efids_list (cgra g a))) then Some(efids_root (cgra g a)) else None)"
definition efid_to_roots :: "[igraph, efid] \<Rightarrow> efid option set"
  where "efid_to_roots g e = efid_to_root g e ` (actors_graph g)"
definition option_set_to_set :: "('a option) set \<Rightarrow> 'a set"
  where "option_set_to_set s = the ` s"
definition opset :: "('a option) set \<Rightarrow> 'a set"
  where "opset s = option_set_to_set(s - {None})"
definition efid_to_root_acts :: "[igraph, identity set, efid] \<Rightarrow> efid option set"
  where "efid_to_root_acts g as e = efid_to_root g e ` as"



lemma sel_def: "the (Some x) = x"
  by simp

theorem option_set_def_lem: "\<forall> x \<in> (option_set_to_set (s -{None})). \<exists> y \<in> s. Some x = y"
  by (simp add: option_set_to_set_def)

lemma opset_lem: "\<forall> x \<in> (opset s). (\<exists> y \<in> s. Some x = y)"
  apply (unfold opset_def)
  by (rule option_set_def_lem)

lemma efid_to_root_inj_lem: "e \<in> (set (efids_list (cgra g a))) \<Longrightarrow> 
                           e' \<in> (set (efids_list (cgra g a'))) \<Longrightarrow> a \<noteq> a' \<Longrightarrow>
             a \<in> actors_graph g \<Longrightarrow> a' \<in> actors_graph g \<Longrightarrow>
            \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow> 
               (set (efids_list (cgra g a))) \<inter> (set (efids_list (cgra g a'))) = {} \<Longrightarrow>
              \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow>
                  efids_root (cgra g a) \<noteq> efids_root (cgra g a') \<Longrightarrow>
              efid_to_root g e a \<noteq> efid_to_root g e' a'"
  by (simp add: efid_to_root_def)

lemma efid_to_root_inj_lem0: "\<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow> 
               (set (efids_list (cgra g a))) \<inter> (set (efids_list (cgra g a'))) = {} \<Longrightarrow>
              \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow>
                  efids_root (cgra g a) \<noteq> efids_root (cgra g a') \<Longrightarrow>
             \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g.
                           e \<in> (set (efids_list (cgra g a))) \<longrightarrow>
                           e' \<in> (set (efids_list (cgra g a'))) \<longrightarrow>
              a \<noteq> a' \<longrightarrow> efid_to_root g e a \<noteq> efid_to_root g e' a'"
  by (simp add: efid_to_root_def)


text \<open>We need to work out a set of invariant conditions that describe the relationship between
      the cgras for each actor (their efid_lists including the efids and the efid_root. 
      The function efid_to_root gives the efid root from the efid list of an actor.
      A useful lemma might be to show that if an actor is in a location then one of its
      efids is in the egra of that location. As a consequence, if we apply efid_to_root
      to this egra set of this location, then the efid_root of that actor should be in the
      result set.
      Invariants: 
      If all efids_lists are disjoint, then if every actor is in only one location then the 
      egra sets at all locations should all be disjoint.
      If all egra sets at all locations are disjoint then every efid should only appear in
      exactly one location in an egra set.
      If we apply efid_to_root to an egra set in one location, we should get the set of 
      all efid_roots of all teh efid_lists of the actors at that location.\<close>

lemma efid_to_roots_inj_lem_one: "e \<in> (set (efids_list (cgra g a))) \<Longrightarrow> 
                           e' \<in> (set (efids_list (cgra g a'))) \<Longrightarrow> a \<noteq> a' \<Longrightarrow>
             a \<in> actors_graph g \<Longrightarrow> a' \<in> actors_graph g \<Longrightarrow>
            \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow> 
               (set (efids_list (cgra g a))) \<inter> (set (efids_list (cgra g a'))) = {} \<Longrightarrow>
              \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow>
                  efids_root (cgra g a) \<noteq> efids_root (cgra g a') \<Longrightarrow>
              x \<in> efid_to_roots g e \<Longrightarrow> x \<notin> efid_to_roots g e'"
  apply (rule notI)
  apply (unfold efid_to_roots_def)
  apply (drule_tac e = e and e' = e' in  efid_to_root_inj_lem0, assumption)
  oops

lemma efid_to_roots_inj_lem: "e \<in> (set (efids_list (cgra g a))) \<Longrightarrow> 
                           e' \<in> (set (efids_list (cgra g a'))) \<Longrightarrow> a \<noteq> a' \<Longrightarrow>
             a \<in> actors_graph g \<Longrightarrow> a' \<in> actors_graph g \<Longrightarrow>
            \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow> 
               (set (efids_list (cgra g a))) \<inter> (set (efids_list (cgra g a'))) = {} \<Longrightarrow>
              \<forall> a \<in> actors_graph g. \<forall> a' \<in> actors_graph g. a \<noteq> a' \<longrightarrow>
                  efids_root (cgra g a) \<noteq> efids_root (cgra g a') \<Longrightarrow>
              efid_to_roots g e \<inter> efid_to_roots g e' = {}"
  apply (drule_tac x = a in bspec, assumption)
  apply (drule_tac x = a' in bspec, assumption)
  apply (drule_tac x = a in bspec, assumption)
  apply (drule_tac x = a' in bspec, assumption)
  apply simp
  apply (subgoal_tac "~(\<exists> x. x \<in> efid_to_roots g e \<inter> efid_to_roots g e')", blast)
  apply (rule notI)
  apply (erule exE, simp)
  apply (erule conjE)
  apply (simp add: efid_to_roots_def efid_to_root_def efids_root_def actors_graph_def)
  oops

*)

text \<open>Predicates and projections for the labels to encode their meaning.\<close>
definition owner :: "dlm * data \<Rightarrow> actor" where "owner d \<equiv> fst(fst d)"
definition owns :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"
  where "owns G l a d \<equiv> owner d = a"
definition readers :: "dlm * data \<Rightarrow> actor set"
  where "readers d \<equiv> snd (fst d)"

text \<open>The predicate @{text \<open>has_access\<close>} is true for owners or readers.\<close> 
definition has_access :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"

typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
  by (fastforce)

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" (infixr "\<Updown>" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 

definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "misbehaviour I \<equiv> -(behaviour I)"

primrec jonce :: "['a, 'a list] \<Rightarrow> bool"
where
jonce_nil: "jonce a [] = False" |
jonce_cons: "jonce a (x#ls) = (if x = a then (a \<notin> (set ls)) else jonce a ls)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                            (cgra g)(n := efids_inc_ind(cgra g n))
                      else (cgra g))
                                 (lgra g)
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then
                       ((egra g)(l := (egra g l) - {efids_cur(cgra g n)}))
                                (l' := insert (efids_cur(efids_inc_ind(cgra g n)))(egra g l))
                      else egra g)(kgra g)"

definition put_graph_efid :: "[identity, location, igraph] \<Rightarrow> igraph"
  where \<open>put_graph_efid n l g  \<equiv> Lgraph (gra g)(agra g)
                            ((cgra g)(n := efids_inc_ind(cgra g n)))
                               (lgra g)
                             ((egra g)(l :=  insert (efids_cur(efids_inc_ind(cgra g n)))
                                           ((egra g l) - {efids_cur(cgra g n)})))
                              (kgra g)\<close>

inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l;
        enables I l (Actor a) get;
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)(egra g)
                       ((kgra g)((Actor a) := ((kgra g (Actor a))(l:= {(x,y). x \<in> agra G l \<and> y \<in> egra G l})))))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        I' = Infrastructure (put_graph_efid a l (graphI I))(delta I)
          \<Longrightarrow> I \<rightarrow>\<^sub>n I'"

text \<open>Note that the type infrastructure can now be instantiated to the axiomatic type class 
      @{text\<open>state\<close>} which enables the use of the underlying Kripke structures and CTL.\<close>
instantiation "infrastructure" :: state
begin
definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

end


lemma move_graph_eq: "move_graph_a a l l g = g"  
  by (simp add: move_graph_a_def, case_tac g, force)

definition ref_map :: "[InfrastructureTwo.infrastructure, 
                        [InfrastructureOne.igraph, location] \<Rightarrow> policy set]
                        \<Rightarrow> InfrastructureOne.infrastructure"
  where "ref_map I lp = InfrastructureOne.Infrastructure 
                                 (InfrastructureOne.Lgraph
                                        (InfrastructureTwo.gra (graphI I))
                                        (InfrastructureTwo.agra (graphI I))
                                        (InfrastructureTwo.cgra (graphI I))
                                        (InfrastructureTwo.lgra (graphI I))
                                        (InfrastructureTwo.egra (graphI I))
                                        (InfrastructureTwo.kgra (graphI I)))   
                                                         lp"

end

 