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
                           "identity \<Rightarrow> (string set * string set * efid)"  
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
primrec cgra :: "igraph \<Rightarrow> (identity \<Rightarrow> string set * string set * efid)"
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

text \<open>There are projection functions text{@ \<open>graphI\<close>} and text{@ \<open>delta\<close>} when applied
to an infrastructure return the graph and the policy, respectively. Other projections
are introduced for the labels, the credential, and roles and to express their meaning.\<close>
primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, identity ] \<Rightarrow> string set * string set * efid"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string * (dlm * data)set"
  where "lspace (Infrastructure g d) = lgra g"

definition credentials :: "string set * string set * efid \<Rightarrow> string set"
  where  "credentials lxl \<equiv> (fst lxl)"
definition has :: "[igraph, identity * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string set * string set * efid \<Rightarrow> string set"
  where  "roles lxl \<equiv> (fst (snd lxl))"
definition efemid :: "string set * string set * efid \<Rightarrow> efid"
  where "efemid lxl \<equiv> snd(snd lxl)"
definition role :: "[igraph, identity * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"
definition isin :: "[igraph,location, string] \<Rightarrow> bool" 
  where "isin G l s \<equiv> s = fst (lgra G l)"

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
                       ((egra g)(l := (egra g l) - {efemid (cgra g n)}))
                                (l' := (insert (efemid (cgra g n))(egra g l')))
                      else egra g)
                               (kgra g)"

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
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l;
        enables I l (Actor a) get;
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)(lgra G)(egra G)
                       ((kgra G)((Actor a) := ((kgra G (Actor a))(l:= {(x,y). x \<in> agra G l \<and> y \<in> egra G l})))))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"

(* 
| get_data : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l' (Actor a) get \<Longrightarrow> 
       ((Actor a', as), n) \<in> snd (lgra G l') \<Longrightarrow> Actor a \<in> as \<Longrightarrow> 
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (fst (lgra G l), 
                                   snd (lgra G l)  \<union> {((Actor a', as), n)}))) 
                            (egra G))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| process : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
        enables I l (Actor a) eval \<Longrightarrow> 
       ((Actor a', as), n) \<in> snd (lgra G l) \<Longrightarrow> Actor a \<in> as \<Longrightarrow>
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)(cgra G)
                   ((lgra G)(l := (fst (lgra G l), 
                    snd (lgra G l)  - {((Actor a', as), n)}
                    \<union> {(f :: label_fun) \<Updown> ((Actor a', as), n)})))
                           (egra G))
                   (delta I)
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| put : "G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow> enables I l (Actor a) put \<Longrightarrow>
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)
                          ((lgra G)(l := (s, snd (lgra G l) \<union> {((Actor a, as), n)})))(egre G))
                   (delta I)
          \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
*)
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
     
end

  