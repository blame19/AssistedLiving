
;// PATH

(defmodule PATH (import MAIN ?ALL) (import AGENT ?ALL) (import PLANNER ?ALL))


;//_______Facts

(deftemplate path (slot id) (slot from-r) (slot from-c) (slot start-dir) (slot to-r) (slot to-c) (slot min-step) (slot cost-estimate) (slot last-step))
(deftemplate path-step (slot id) (slot step) (slot pos-r) (slot pos-c) (slot direction))

(deftemplate id-counter (slot id))

;//_______Functions

;//_______Rules
(defrule initialize 
	(declare (salience 11))
	(not (id-counter (id ?id)))
	=>
	(assert (id-counter (id 0)))
)

;trasforma le posizioni di candidate-goal-pos in oggetti path, di cui poi stimerà il costo e il percorso
(defrule path_request 
	(K-agent (pos-r ?rA) (pos-c ?cA) (direction ?dir))
	(candidate-goal-pos (pos-r ?r) (pos-c ?c))
	
	=>
	(assert (path (from-r ?rA) (from-c ?cA) (start-dir ?dir) (to-r ?r) (to-c ?c) ))
	
)

;Calcola una sottostima del numero di step necessari a completare il cammino
;una distanza di minkosky tra la posizione di start ed end
(defrule path_min_step 
	?f <- (path (id nil) (from-r ?rA) (from-c ?cA) (start-dir ?dir) (to-r ?r) (to-c ?c) (min-step nil))
	?e <- (id-counter (id ?id))
	=>
	(modify ?f (min-step (+ (abs (- ?rA ?r)) (abs (- ?cA ?c)) ) ) (id ?id) )
	(modify ?e (id (+ ?id 1)))	
)

;(defrule generate_path_step
;	? <- (path (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sd) (to-r ?tr) (to-c ?tc) (min-step ?ms) (cost-estimate ?ce))
;	(not (path-step (id ?id) (pos-r ?tr) (pos-c ?tc)))
;
;)

