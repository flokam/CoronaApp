section \<open>Infrastructures\<close>
text \<open>The Isabelle Infrastructure framework supports the representation of infrastructures 
as graphs with actors and policies attached to nodes. These infrastructures 
are the {\it states} of the Kripke structure. 
The transition between states is triggered by non-parametrized
actions @{text \<open>get, move, eval, put\<close>} executed by actors. 
Actors are given by an abstract type @{text \<open>actor\<close>} and a function 
@{text \<open>Actor\<close>} that creates elements of that type from identities 
(of type @{text \<open>string\<close>}). Policies are given by pairs of predicates 
(conditions) and sets of (enabled) actions.\<close>
subsection \<open>Actors, actions, and data labels\<close>
theory Infrastructure
  imports Refinement
begin
datatype action = get | move | eval | put

typedecl actor 
type_synonym identity = string
consts Actor :: "string \<Rightarrow> actor"
type_synonym policy = "((actor \<Rightarrow> bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
  where "ID a s \<equiv> (a = Actor s)"
text \<open>The Decentralised Label Model (DLM) \cite{ml:98} introduced the idea to
label data by owners and readers. We pick up this idea and formalize
a new type to encode the owner and the set of readers as a pair.
The first element is the owner of a data item, the second one is the
set of all actors that may access the data item.
This enables the unique security 
labelling of data within the system additionally taking the ownership into 
account.\<close>
type_synonym data = nat  
type_synonym dlm = "actor * actor set"

subsection \<open>Infrastructure graphs and policies\<close>
text\<open>Actors are contained in an infrastructure graph. An @{text \<open>igraph\<close>} contains
a set of location pairs representing the topology of the infrastructure
as a graph of nodes and a list of actor identities associated to each node 
(location) in the graph.
Also an @{text \<open>igraph\<close>} associates actors to a pair of string sets by
a pair-valued function whose first range component is a set describing
the credentials in the possession of an actor and the second component
is a set defining the roles the actor can take on. More importantly in this 
context, an  @{text \<open>igraph\<close>} assigns locations to a pair of a string that defines
the state of the component and an element of type @{text \<open>(dlm * data) set\<close>}. This
set of labelled data may represent a condition on that data.
Corresponding projection functions for each of these components of an 
@{text \<open>igraph\<close>} are provided; they are named @{text \<open>gra\<close>} for the actual set of pairs of
locations, @{text \<open>agra\<close>} for the actor map, @{text \<open>cgra\<close>} for the credentials,
and @{text \<open>lgra\<close>} for the state of a location and the data at that location.
Finally, there is the map of the (Efemeral) Ids that are posted by mobile phones at a location
(which is added here for the CoronaApp) and the map for each actor to the knowledge set which
represents the combinatorial explosion of all Ids with all people present at a location representing the
knowledge about who might be who. \<close>
datatype location = Location nat
datatype efid = Efid nat
datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity set"
                           "identity \<Rightarrow>  efid"  
                           "location \<Rightarrow> string * (dlm * data) set"
                           "location \<Rightarrow> efid set"
                           "identity \<Rightarrow> location \<Rightarrow> (identity * efid)set"

datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph, location] \<Rightarrow> policy set" 
                       
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l e k) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity set)"
where  "agra(Lgraph g a c l e k) = a"
primrec cgra :: "igraph \<Rightarrow> identity \<Rightarrow> efid"
where  "cgra(Lgraph g a c l e k) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string * (dlm * data) set)"
  where  "lgra(Lgraph g a c l e k) = l"
primrec egra :: "igraph \<Rightarrow> location \<Rightarrow> efid set"
  where  "egra(Lgraph g a c l e k) = e"
primrec kgra:: "[igraph, identity, location] \<Rightarrow> (identity * efid)set"
  where "kgra(Lgraph g a c l e k) = k"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> (agra g y)}"

text \<open>There are projection functions text{@ \<open>graphI\<close>} and text{@ \<open>delta\<close>} when applied
to an infrastructure return the graph and the policy, respectively. Other projections
are introduced for the labels, the credential, and roles and to express their meaning.\<close>
primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, identity ] \<Rightarrow> efid"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string * (dlm * data)set"
  where "lspace (Infrastructure g d) = lgra g"


text \<open>Predicates and projections for the labels to encode their meaning.\<close>
definition owner :: "dlm * data \<Rightarrow> actor" where "owner d \<equiv> fst(fst d)"
definition owns :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"
  where "owns G l a d \<equiv> owner d = a"
definition readers :: "dlm * data \<Rightarrow> actor set"
  where "readers d \<equiv> snd (fst d)"

text \<open>The predicate @{text \<open>has_access\<close>} is true for owners or readers.\<close> 
definition has_access :: "[igraph, location, actor, dlm * data] \<Rightarrow> bool"    
where "has_access G l a d \<equiv> owns G l a d \<or> a \<in> readers d"

(*
text \<open>Actors can delete data.\<close>
definition actor_can_delete ::   "[infrastructure, actor, location] \<Rightarrow> bool"
where actor_can_delete_def: "actor_can_delete I h l \<equiv>  
                   (\<forall> as n. ((h, as), n) \<notin> (snd (lgra (graphI I) l)))"
*)
text \<open>We define a type of functions that preserves the security labeling and a 
   corresponding function application  operator.\<close>  
typedef label_fun = "{f :: dlm * data \<Rightarrow> dlm * data. 
                        \<forall> x:: dlm * data. fst x = fst (f x)}"  
  by (fastforce)

definition secure_process :: "label_fun \<Rightarrow> dlm * data \<Rightarrow> dlm * data" (infixr "\<Updown>" 50)
  where "f  \<Updown> d \<equiv> (Rep_label_fun f) d" 

(*
subsection \<open>Insider predicate\<close>
text \<open>The human actor's level is modelled in the Isabelle Insider framework by assigning
the individual actor's psychological disposition\footnote{Note that the determination of 
the psychological state of an actor is not done using the formal system. It is up to a 
psychologist to determine this. However, if for instance, an actor is classified as 
@{text \<open>disgruntled\<close>} then this may have an influence on what they are allowed to do according 
to a company policy and this can be formally described and reasoned about in Isabelle.} 
@{text \<open>actor_state\<close>} to each actor's identity.\<close>
datatype psy_states = happy | depressed | disgruntled | angry | stressed
datatype motivations = financial | political | revenge | curious | competitive_advantage | power | peer_recognition

text \<open>The values used for the definition of the types
@{text \<open>motivations\<close>} and @{text \<open>psy_state\<close>}
are based on a taxonomy from psychological insider research \cite{nblgcww:14}.
The transition to become an insider is represented by a {\it Catalyst} that tips the insider 
over the edge so he acts as an insider formalized as a ``tipping point'' 
predicate.\<close>
datatype actor_state = Actor_state "psy_states" "motivations set"
primrec motivation :: "actor_state \<Rightarrow> motivations set" 
where "motivation  (Actor_state p m) =  m"
primrec psy_state :: "actor_state \<Rightarrow> psy_states" 
where "psy_state  (Actor_state p m) = p"

definition tipping_point :: "actor_state \<Rightarrow> bool" where
  "tipping_point a \<equiv> ((motivation a \<noteq> {}) \<and> (happy \<noteq> psy_state a))"

text \<open>To embed the fact that the attacker is an insider, the actor can then
impersonate other actors. In the Isabelle Insider framework, the 
predicate @{text \<open>Insider\<close>} must be used as a {\it locale} assumption
to enable impersonation for the insider:
this assumption entails that an insider @{text \<open>Actor ''Eve''\<close>} can act like 
their alter ego, say @{text \<open>Actor ''Charly''\<close>} within the context of the locale.
This is realized by the predicate  @{text \<open>UasI\<close>}:
@{text \<open>UasI\<close>} and @{text \<open>UasI'\<close>} are the central predicates allowing to specify Insiders.
They define which identities can be mapped to the same role by the @{text \<open>Actor\<close>} function
(an impersonation predicate "@{text \<open>a\<close>} can act as @{text \<open>b\<close>}").
For all other identities, @{text \<open>Actor\<close>} is defined as injective on those identities.
The first one is stronger and allows substitution of the insider in any context; the second 
one is parameterized over a context predicate to describe this.\<close>
definition UasI ::  "[identity, identity] \<Rightarrow> bool " 
where "UasI a b \<equiv> (Actor a = Actor b) \<and> (\<forall> x y. x \<noteq> a \<and> y \<noteq> a \<and> Actor x = Actor y \<longrightarrow> x = y)"
definition UasI' ::  "[actor \<Rightarrow> bool, identity, identity] \<Rightarrow> bool " 
where "UasI' P a b \<equiv> P (Actor b) \<longrightarrow> P (Actor a)"

text \<open>Two versions of Insider predicate corresponding to @{text \<open>UasI\<close>} and @{text \<open>UasI'\<close>}
exist. Under the assumption that the tipping point has been reached for a person @{text \<open>a\<close>}
then @{text \<open>a\<close>} can impersonate all @{text \<open>b\<close>} (take all of @{text \<open>b\<close>}'s "roles") where
the @{text \<open>b\<close>}'s are specified by a given set of identities.\<close>
definition Insider :: "[identity, identity set, identity \<Rightarrow> actor_state] \<Rightarrow> bool" 
where "Insider a C as \<equiv> (tipping_point (as a) \<longrightarrow> (\<forall> b\<in>C. UasI a b))"
definition Insider' :: "[actor \<Rightarrow> bool, identity, identity set, identity \<Rightarrow> actor_state] \<Rightarrow> bool" 
where "Insider' P a C as \<equiv> (tipping_point (as a) \<longrightarrow> (\<forall> b\<in>C. UasI' P a b \<and> inj_on Actor C))"
*)
text \<open>The predicate atI -- mixfix syntax @{text \<open>@\<^bsub>G\<^esub>\<close>} -- expresses that an actor (identity) 
      is at a certain location in an igraph.\<close>
definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (agra G l)"

text \<open>Policies specify the expected behaviour of actors of an infrastructure. 
They are defined by the @{text \<open>enables\<close>} predicate:
an actor @{text \<open>h\<close>} is enabled to perform an action @{text \<open>a\<close>} 
in infrastructure @{text \<open>I\<close>}, at location @{text \<open>l\<close>}
if there exists a pair @{text \<open>(p,e)\<close>} in the local policy of @{text \<open>l\<close>}
(@{text \<open>delta I l\<close>} projects to the local policy) such that the action 
@{text \<open>a\<close>} is a member of the action set @{text \<open>e\<close>} and the policy 
predicate @{text \<open>p\<close>} holds for actor @{text \<open>h\<close>}.\<close>
definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

text \<open>The behaviour is the good behaviour, i.e. everything allowed by the policy of infrastructure I.\<close>
definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

text \<open>The misbehaviour is the complement of the behaviour of an infrastructure I.\<close>
definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "misbehaviour I \<equiv> -(behaviour I)"

subsection "State transition on infrastructures"
text \<open>The state transition defines how actors may act on infrastructures through actions
    within the boundaries of the policy. It is given as an inductive definition over the 
    states which are infrastructures.  This state transition relation is dependent on actions but also on
    enabledness and the current state of the infrastructure.

    First we introduce some auxiliary functions dealing
    with repetitions in lists and actors moving in an igraph.\<close>
primrec jonce :: "['a, 'a list] \<Rightarrow> bool"
where
jonce_nil: "jonce a [] = False" |
jonce_cons: "jonce a (x#ls) = (if x = a then (a \<notin> (set ls)) else jonce a ls)"
(*
primrec nodup :: "['a, 'a list] \<Rightarrow> bool"
  where 
    nodup_nil: "nodup a [] = True" |
    nodup_step: "nodup a (x # ls) = (if x = a then (a \<notin> (set ls)) else nodup a ls)"
*)
text \<open>The @{text \<open>move_graph_a\<close>} function encapsulates the infrastructure state change for a 
      move action used in the subsequent rule move. It relocates the actor from a location l
      to a new location l' if the actor is actually at l and is not at l'. Additionally, 
      here for the CoronaApp application, under the same conditons the local sending of the
      ephemeral Id of the actor is also moved to the new location l' by adapting the egra component
      of the infrastructure state graph.\<close>
definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then 
                     ((agra g)(l := (agra g l) - {n}))(l' := (insert n (agra g l')))
                     else (agra g))
                               (cgra g)(lgra g)
                     (if n \<in> ((agra g) l) &  n \<notin> ((agra g) l') then
                       ((egra g)(l := (egra g l) - {cgra g n}))
                                (l' := (insert (cgra g n)(egra g l')))
                      else egra g)
                               (kgra g)"

definition put_graph_efid :: "[identity, location, igraph] \<Rightarrow> igraph"
  where \<open>put_graph_efid n l g  \<equiv> Lgraph (gra g)(agra g)
                               (cgra g)
                               (lgra g)
                             ((egra g)(l := insert ((cgra g n))(egra g l)))
                              (kgra g)\<close>

text \<open>The state transition relation defines the semantics for the actions. We concentrate
     only on two: move and get. Move models the moving of actors from one locations to another
     automatically posting the ephemeral ids at the new location (and stop posting them at the 
     old location, i.e. deleting them there) -- this is implemented in @{text \<open>move_graph_a\<close>}
     above.
     For get, an actor a at a location can use get, if he's entitled to do that by the policy, 
     to extend hos knowledge set. He adds all combinations of the actors a sees at the location 
     with all ephemeral ids she measures, i.e. which are in the set @{text \<open>egra G l\<close>}. If a
     already has a nonempty knowledge set @{text \<open>kgra G (Actor a)\<close>} she can already improve
     her knowledge by building an intersection with the previous knowledge set.\<close>
inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G;
        enables I l (Actor a) get;
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)(egra G)
                       ((kgra G)(a := ((kgra G a)(l:= {(x,y). x \<in> agra G l \<and> y \<in> egra G l})))))
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


lemma delta_invariant: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"
  apply clarify
  apply (erule state_transition_in.cases)
  by simp+

lemma same_actors0[rule_format]: "\<forall> z z'.  z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph (graphI z) = actors_graph (graphI z')"
proof (clarify, erule state_transition_in.cases)
  show "\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z')"
    apply (simp add: actors_graph_def)
    apply (rule equalityI)
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE, erule conjE)+
    apply (simp add: move_graph_a_def)
proof -
  fix z :: infrastructure and z' :: infrastructure and G :: igraph and I :: infrastructure and a :: "char list" and l :: location and l' :: location and I' :: infrastructure and x :: "char list" and y :: location and ya :: location
assume a1: "x \<in> agra (graphI I) ya"
assume a2: "ya \<in> nodes (graphI I)"
assume a3: "l' \<in> nodes (graphI I)"
assume "l \<in> nodes (graphI I)"
  have f4: "\<forall>f fa fb fc fd i. nodes (Lgraph (gra i) f fd fa fc fb) = nodes i"
by (simp add: nodes_def)
obtain bb :: bool where
f5: "bb = ((a \<notin> agra (graphI I) l \<or> a \<in> agra (graphI I) l') \<or> (\<exists>X56. (X56 \<noteq> l \<or> (l \<noteq> l' \<or> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I))(l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (l = l' \<or> l \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) l \<and> x \<noteq> a)) \<and> (X56 = l \<or> (X56 \<noteq> l' \<or> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (X56 = l' \<or> X56 \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) X56))))"
by blast
then have "bb \<and> (a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l' \<or> bb \<and> (\<exists>l. l \<in> nodes (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I)) (egra (graphI I)) (kgra (graphI I))) \<and> x \<in> agra (graphI I) l))"
using f4 a3 a2 a1 by metis
then show "(a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I))(l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) la)))) \<and> ((a \<in> agra (graphI I) l \<longrightarrow> a \<in> agra (graphI I) l') \<longrightarrow> (a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l' \<longrightarrow> (\<exists>la. (la = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I))(l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) l \<and> x \<noteq> a)) \<and> (la \<noteq> l \<longrightarrow> (la = l' \<longrightarrow> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> la \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) la)))) \<and> (\<exists>l. l \<in> nodes (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I)) (egra (graphI I)) (kgra (graphI I))) \<and> x \<in> agra (graphI I) l))"
  using f5 by blast
next show "\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       \<exists>y. y \<in> nodes (graphI I) \<and> a \<in> agra (graphI I) y \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       {x. \<exists>y. y \<in> nodes (move_graph_a a l l' (graphI I)) \<and> x \<in> agra (move_graph_a a l l' (graphI I)) y}
       \<subseteq> {x. \<exists>y. y \<in> nodes (graphI I) \<and> x \<in> agra (graphI I) y}"
    apply (simp add: enables_def move_graph_a_def)
    apply (rule conjI)
     apply (rule impI)+
     apply (rule subsetI)
     apply (rule CollectI)
     apply (drule CollectD)
     apply (erule exE)+
    apply (erule conjE)+
  proof -
    fix z :: infrastructure and z' :: infrastructure and G :: igraph and I :: infrastructure and a :: "char list" and l :: location and l' :: location and I' :: infrastructure and x :: "char list" and y :: location and ya :: location
    assume a1: "G = graphI I"
    assume a2: "ya = l \<longrightarrow> (l = l' \<longrightarrow> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I))(l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (l \<noteq> l' \<longrightarrow> l \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) l \<and> x \<noteq> a)"
    assume a3: "l \<in> nodes (graphI I)"
    assume a4: "l' \<in> nodes (graphI I)"
    assume a5: "a \<in> agra (graphI I) y"
    assume a6: "ya \<noteq> l \<longrightarrow> (ya = l' \<longrightarrow> l' \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> (x = a \<or> x \<in> agra (graphI I) l')) \<and> (ya \<noteq> l' \<longrightarrow> ya \<in> nodes (Lgraph (gra (graphI I)) ((agra (graphI I)) (l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l'))) (cgra (graphI I)) (lgra (graphI I)) ((egra (graphI I)) (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))) (kgra (graphI I))) \<and> x \<in> agra (graphI I) ya)"
    assume a7: "y \<in> nodes (graphI I)"
    have "ya = l' \<or> ya = l \<or> (\<exists>l. x \<in> agra G l \<and> l \<in> nodes G)"
      using a6 a1 nodes_def by force
    then show "\<exists>l. l \<in> nodes (graphI I) \<and> x \<in> agra (graphI I) l"
      using a7 a6 a5 a4 a3 a2 a1 by (metis (full_types))
  next show "\<And>z z' G I a l l' I'.
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l'
           then (agra (graphI I))(l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l')) else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I))
          (if a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l'
           then (egra (graphI I))
                (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))
           else egra (graphI I))
          (kgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       \<exists>y. y \<in> nodes (graphI I) \<and> a \<in> agra (graphI I) y \<Longrightarrow>
       \<exists>x\<in>delta I (graphI I) l'. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a) \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l'
           then (agra (graphI I))(l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l')) else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I))
          (if a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l'
           then (egra (graphI I))
                (l := egra (graphI I) l - {cgra (graphI I) a}, l' := insert (cgra (graphI I) a) (egra (graphI I) l'))
           else egra (graphI I))
          (kgra (graphI I)))
        (delta I) \<Longrightarrow>
       (a \<in> agra (graphI I) l \<longrightarrow> a \<in> agra (graphI I) l') \<longrightarrow>
       (a \<in> agra (graphI I) l \<and> a \<notin> agra (graphI I) l' \<longrightarrow>
        {x. \<exists>y. (y = l \<longrightarrow>
                 (l = l' \<longrightarrow>
                  l' \<in> nodes
                         (Lgraph (gra (graphI I)) ((agra (graphI I))(l' := insert a (agra (graphI I) l')))
                           (cgra (graphI I)) (lgra (graphI I))
                           ((egra (graphI I))(l' := insert (cgra (graphI I) a) (egra (graphI I) l')))
                           (kgra (graphI I))) \<and>
                  (x = a \<or> x \<in> agra (graphI I) l')) \<and>
                 (l \<noteq> l' \<longrightarrow>
                  l \<in> nodes
                        (Lgraph (gra (graphI I))
                          ((agra (graphI I))(l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l')))
                          (cgra (graphI I)) (lgra (graphI I))
                          ((egra (graphI I))
                           (l := egra (graphI I) l - {cgra (graphI I) a},
                            l' := insert (cgra (graphI I) a) (egra (graphI I) l')))
                          (kgra (graphI I))) \<and>
                  x \<in> agra (graphI I) l \<and> x \<noteq> a)) \<and>
                (y \<noteq> l \<longrightarrow>
                 (y = l' \<longrightarrow>
                  l' \<in> nodes
                         (Lgraph (gra (graphI I))
                           ((agra (graphI I))(l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l')))
                           (cgra (graphI I)) (lgra (graphI I))
                           ((egra (graphI I))
                            (l := egra (graphI I) l - {cgra (graphI I) a},
                             l' := insert (cgra (graphI I) a) (egra (graphI I) l')))
                           (kgra (graphI I))) \<and>
                  (x = a \<or> x \<in> agra (graphI I) l')) \<and>
                 (y \<noteq> l' \<longrightarrow>
                  y \<in> nodes
                        (Lgraph (gra (graphI I))
                          ((agra (graphI I))(l := agra (graphI I) l - {a}, l' := insert a (agra (graphI I) l')))
                          (cgra (graphI I)) (lgra (graphI I))
                          ((egra (graphI I))
                           (l := egra (graphI I) l - {cgra (graphI I) a},
                            l' := insert (cgra (graphI I) a) (egra (graphI I) l')))
                          (kgra (graphI I))) \<and>
                  x \<in> agra (graphI I) y))}
        \<subseteq> {x. \<exists>y. y \<in> nodes (graphI I) \<and> x \<in> agra (graphI I) y}) \<and>
       {x. \<exists>y. y \<in> nodes
                     (Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I)) (egra (graphI I))
                       (kgra (graphI I))) \<and>
               x \<in> agra (graphI I) y}
       \<subseteq> {x. \<exists>y. y \<in> nodes (graphI I) \<and> x \<in> agra (graphI I) y} "
      using nodes_def by auto
  qed
qed
next show "\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (put_graph_efid a l (graphI I)) (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z') "
    by (simp add: actors_graph_def nodes_def put_graph_efid_def)
next show "\<And>z z' G I a l I'.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra G) (agra G) (cgra G) (lgra G) (egra G)
          ((kgra G)(a := (kgra G a)(l := {(x, y). x \<in> agra G l \<and> y \<in> egra G l}))))
        (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z') "
    by (simp add: actors_graph_def nodes_def)
qed

lemma same_actors: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI I) = actors_graph(graphI y)"
proof (erule rtrancl_induct)
  show "actors_graph (graphI I) = actors_graph (graphI I)"
    by (rule refl)
next show "\<And>(y::infrastructure) z::infrastructure.
       (I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI y) \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI z)"
    by (drule CollectD, simp, drule same_actors0, simp)  
qed


(* locations invariants *)
 lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
    apply clarify
  apply (erule Infrastructure.state_transition_in.cases)
  by (simp add: move_graph_a_def atI_def actors_graph_def nodes_def put_graph_efid_def)+

lemma same_nodes: "(c, s) \<in> {(x::Infrastructure.infrastructure, y::Infrastructure.infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
\<Longrightarrow> Infrastructure.nodes (graphI c) = Infrastructure.nodes (graphI s)"
  apply (erule rtrancl_induct)
   apply (rule refl)
  apply (drule CollectD)
    apply simp
    apply (drule same_nodes0)
  by simp  

(* delta invariants *)
lemma init_state_policy0: "\<lbrakk> \<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z'); 
                          (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  apply (rule mp)
  prefer 2
   apply (rotate_tac 1)
    apply assumption
  thm rtrancl_induct
  apply (erule rtrancl_induct)  
    apply (rule impI)
   apply (rule refl)
    apply (subgoal_tac "delta y = delta z")
   apply (erule impE)
    apply assumption
    apply (rule impI)
   apply (rule trans)
    apply assumption+
  apply (drule_tac x = y in spec)
  apply (drule_tac x = z in spec)
    apply (rotate_tac -1)
  apply (erule impE)
    apply simp
by assumption
 
lemma init_state_policy: "\<lbrakk> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  apply (rule init_state_policy0)
    apply (rule delta_invariant)
  by assumption

(* efids invariants *)
lemma eroots_inj_inv0: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  
inj(cgra (graphI z)) \<longrightarrow> inj (cgra (graphI z'))"
    apply clarify
  apply (erule Infrastructure.state_transition_in.cases)
  apply (simp add: move_graph_a_def)
  apply simp
  by (simp add: put_graph_efid_def)

lemma eroots_inj_inv: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> inj(cgra (graphI I)) \<longrightarrow> inj (cgra (graphI y))"
proof (erule rtrancl_induct)
  show "inj (cgra (graphI I)) \<longrightarrow> inj (cgra (graphI I))" by simp
next show "\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           inj (cgra (graphI I)) \<longrightarrow> inj (cgra (graphI y)) \<Longrightarrow> inj (cgra (graphI I)) \<longrightarrow> inj (cgra (graphI z)) "
    using eroots_inj_inv0 by auto
qed


end

  