
;// PATH

(defmodule PATH (import MAIN ?ALL) (import AGENT ?ALL) (import PLANNER ?ALL))


;//_______Facts

(deftemplate path 
	(slot id) 
	(slot from-r) 
	(slot from-c) 
	(slot start-dir) 
	(slot to-r) 
	(slot to-c) 
	(slot cost) 
	(slot solution (allowed-values yes no) (default no))
)

;Ogni nodo ha:
; 1) id del path
; 2) id del nodo
; 3) id del nodo-padre
; 4) coordinate, costo effettivo e costo euristica
; 5) direzione (che ha l'agente quando entra nella cella del nodo)
(deftemplate node (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot cost-real) (slot cost-heur) (slot direction))


(deftemplate generate-path-steps (slot path-id) (slot node-translate) (slot clean-all (allowed-values no yes) (default no)))


(deftemplate frontier (slot path-id) (slot father-id) (slot node-r) (slot node-c) (slot cost-real) (slot cost-heur) (slot cost-total (default 0)) (slot direction))
		

;TODO: meglio tenere l'id counter dei nodi univoci solo relativamente allo stesso path, quindi andrà riazzerato una volta finito di considerare un path
(deftemplate id-counter (slot id))

;//_______Functions

(deffunction manhattan (?r1 ?c1 ?r2 ?c2)
	(if (or (= (- ?r1 ?r2) 0) (= (- ?c1 ?c2) 0)) 
		then (+ (abs(- ?r1 ?r2)) (abs(- ?c1 ?c2)))

		else (+ (abs(- ?r1 ?r2)) (abs(- ?c1 ?c2)) 2) 
	)
)

(deffunction relative_direction (?r1 ?c1 ?r2 ?c2)
	(if (and (= ?r1 ?r2) (< ?c1 ?c2)) 
		then east	
		else
		(if (and (= ?r1 ?r2) (> ?c1 ?c2 )) 
		then west else 
		(if (and (= ?c1 ?c2) (< ?r1 ?r2)) 
		then north else 
		(if (and (= ?c1 ?c2) (> ?r1 ?r2)) 
		then south else undefined))))
)

;//_______Rules
(defrule initialize 
	(declare (salience 11))
	(not (id-counter (id ?id)))
	=>
	(assert (id-counter (id 0)))
)

;trasforma le posizioni di candidate-goal-pos in oggetti path, di cui poi stimerà il costo e il percorso
(defrule path_request 
	(declare (salience 6))
	(K-agent (pos-r ?rA) (pos-c ?cA) (direction ?dir))
	?f <- (candidate-goal-pos (id ?i) (pos-r ?r) (pos-c ?c))	
	=>
	(assert (path (id ?i) (from-r ?rA) (from-c ?cA) (start-dir ?dir) (to-r ?r) (to-c ?c) ))
	(retract ?f)
	
)

;Calcola una sottostima del numero di step necessari a completare il cammino
;una distanza di minkosky tra la posizione di start ed end
; (defrule path_min_step
; 	(declare (salience 11))
; 	?f <- (path (from-r ?rA) (from-c ?cA) (start-dir ?dir) (to-r ?r) (to-c ?c) (min-step nil))	
; 	=>
; 	;se il percorso è una linea retta, allora l'agente non dovrà girarsi durante il cammino
; 	(if (or (= (- ?rA ?r) 0) (= (- ?cA ?c) 0))  then 
; 		(modify ?f (min-step (+ (abs (- ?rA ?r)) (abs (- ?cA ?c)) ) ) )
; 	else		
; 		(modify ?f (min-step (+ (abs (- ?rA ?r)) (abs (- ?cA ?c)) 2 ) ) )		
; 	)
	
; )

;inizializza la root del path per l'algoritmo A-STAR
(defrule A_star_root
	(declare (salience 10))
	(path (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?ce) (solution ?found))
	(test (eq ?found no))
	?f <- (id-counter (id ?i))
	(not (node (path-id ?id) (node-r ?fr) (node-c ?fc) (cost-real 0) (direction ?sdir)))
	=>
	(assert (node (path-id ?id) (node-id ?i) (node-r ?fr) (father-id 0) (node-c ?fc) (cost-real 0) (cost-heur (manhattan ?fr ?fc ?tr ?tc)) (direction ?sdir)))
	(modify ?f (id (+ ?id 1)))
)

(defrule A_star_path
	(declare (salience 10))
	(path (id ?id) (start-dir ?sdir) (to-r ?tr) (to-c ?tc)  (cost ?ce) (solution no))
	;considero un nodo
	(node (path-id ?id) (father-id ?fid) (node-id ?i) (node-r ?nr) (node-c ?nc) (cost-real ?cr) (cost-heur ?ch) (direction ?dir))
	;considero anche suo padre, perché ho bisogno delle sue informazioni : non è vero
	(node (path-id ?id) (node-id ?fid) (node-r ?fatherr) (node-c ?fatherc) (direction ?fatherdir))
	(K-cell (pos-r ?kr) (pos-c ?kc) (contains Empty))	
	(test (or  
		(and (= ?kr ?nr) (= ?kc (+ ?nc 1)) )
		(and (= ?kr ?nr) (= ?kc (- ?nc 1)) )
		(and (= ?kr (+ ?nr 1)) (= ?kc ?nc ))
		(and (= ?kr (- ?nr 1)) (= ?kc ?nc))
		)
	)
	;non voglio aggiungere nodi già generati alla frontiera ... forse inutile, non posso generare due fatti uguali
	(not (frontier (path-id ?id) (node-r ?kr) (node-c ?kc)))
	;escludo il padre : non deve essere aggiunto alla frontiera
	(test (not (and (= ?fatherr ?kr) (= ?fatherc ?kc))))
	;ma in generale non voglio nodi già generati nella frontiera
	(not (node (node-r ?kr) (node-c ?kc)))
	=>
	(switch (turn ?dir (relative_direction ?nr ?nc ?kr ?kc)) 
	  (case same 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?kr) (node-c ?kc) (cost-real (+ ?cr 1)) (cost-heur (manhattan ?kr ?kc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) ) )
	  	) 
	  (case right 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?kr) (node-c ?kc) (cost-real (+ ?cr 3)) (cost-heur (manhattan ?kr ?kc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) )) 
	  	)	
	  (case left 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?kr) (node-c ?kc) (cost-real (+ ?cr 3)) (cost-heur (manhattan ?kr ?kc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) )) 
	  	)
	  (case opposite 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?kr) (node-c ?kc) (cost-real (+ ?cr 5)) (cost-heur (manhattan ?kr ?kc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) )) 
	  	)
	  )
	;TODO: rimuovere
	;(assert (frontier (path-id ?id) (node-r ?kr) (node-c ?kc) (cost-real 0) (cost-heur (manhattan ?kr ?tr ?kc ?tc)) (direction ?sdir) ))	
)

(defrule frontier_costs
	(declare (salience 9))
	?e <-(frontier (cost-real ?cr) (cost-heur ?ch) (cost-total 0))
	
	=>
	(modify ?e (cost-total (+ ?cr ?ch)))
	;TODO: rimuovere
	;(assert (frontier (path-id ?id) (node-r ?kr) (node-c ?kc) (cost-real 0) (cost-heur (manhattan ?kr ?tr ?kc ?tc)) (direction ?sdir) ))	
)


(defrule A_star_expand
	(declare (salience 8))
	(path (id ?id) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?ce) (solution no))
	?f <- (id-counter (id ?i))
	;considero un elemento della frontiera
	?e <-(frontier (path-id ?id) (father-id ?fid) (node-r ?nr) (node-c ?nc) (cost-real ?cr) (cost-total ?ct) (cost-heur ?ch) (direction ?dir))
	
	(not (frontier (cost-total ?ct2&:(> ?ct ?ct2))))
	
	;devo trovare quello con costo minimo....		
	=>
	(assert (node (path-id ?id) (node-id ?i) (father-id ?fid) (node-r ?nr) (node-c ?nc) (cost-real ?cr) (cost-heur ?ch)  (direction ?dir) ))
	(retract ?e)
	(modify ?f (id (+ ?i 1)))
)

(defrule A_star_terminate
	(declare (salience 10))	
	?f <- (path (id ?id) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?ce) (solution no))
	?e <- (id-counter)
	(node (path-id ?id) (node-id ?i) (father-id ?fid) (node-r ?tr) (node-c ?tc) (cost-real ?cr) (cost-heur ?ch) (direction ?dir))
	=>
	(modify ?f (solution yes) (cost ?cr))
	(modify ?e (id 0))
	(assert (generate-path-steps (path-id ?id) (node-translate ?i))	)
	)

(defrule generate_path_steps
	(declare (salience 12))
	(path (id ?id))
	?f <- (generate-path-steps (path-id ?id) (node-translate ?x) (clean-all no))
	(node (father-id ?fid) (node-id ?x) (path-id ?id) (node-r ?r) (node-c ?c) (direction ?dir))
	=>
	(assert (path-step (path-id ?id) (node-id ?x) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir)))
	(if (= ?fid ?x 0) then (modify ?f (clean-all yes))
		else (modify ?f (node-translate ?fid))
	)
)


;alla fine di Astar, cancellare tutti i frontier
; tradurre i node in path-step
; cancellare i node

(defrule cleaning_nodes 	
	(declare (salience 12))
	(generate-path-steps (path-id ?id) (clean-all yes))
	?f <- (node (path-id ?id)) 
	=>
	(retract ?f)
	
)

(defrule cleaning_frontier	
	(declare (salience 12))
	(generate-path-steps (path-id ?id) (clean-all yes))
	?e <- (frontier (path-id ?id))
	=>
	(retract ?e)
)

(defrule cleaning_done	
	(declare (salience 12))
	?f <- (generate-path-steps (path-id ?id) (clean-all yes))
	(not (node (path-id ?id)))
	(not (frontier (path-id ?id)))
	=>
	(retract ?f)
)

(defrule choose_one_path
	(declare (salience 4))
	(K-agent (pos-r ?kr) (pos-c ?kc))
	;TODO: aggiungere un sistema di ID per le goal position
	; in modo da poter fare matching con i path id
	?f <- (obj-goal-pos (pos-r ?tr) (pos-c ?tc) (solution-id nil))
	(path (id ?id) (from-r ?kr) (from-c ?kc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?c) (solution yes))
	(not (path (from-r ?kr) (from-c ?kc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?c2&:(< ?c2 ?c)) (solution yes)))
	=>
	(modify ?f (solution-id ?id))
	(pop-focus)

)