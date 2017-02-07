
;// PATH

(defmodule PATH (import MAIN ?ALL) (import AGENT ?ALL) (import STRATEGY ?ALL))


;//_______Facts


;TODO scorpora il PATH dal resto
;TODO rappresenta anche le azioni (girarsi) oltre agli spostamenti
; quindi la funzionalità di action, che traduceva le celle in azioni di spostamento, si sposta qui
;(deftemplate path  (slot id) (slot obj-id)
;	(slot from-r) (slot from-c) 
;	(slot start-dir) 
;	(slot to-r) (slot to-c) 
;	(slot cost) (slot solution (allowed-values yes no) (default no))
;)

;il modulo PATH comunicherà con gli altri tramite path_requests
; chi vuole fare una richiesta dovrà implementare un fatto del tipo
; (deftemplate path-request
; (slot id) (slot from-r) (slot from-c) (slot to-r) (slot to-c) (slot start-dir)
; )
;e poi passare il focus a PATH

;Ogni nodo ha:
; 1) id del path
; 2) id del nodo
; 3) id del nodo-padre
; 4) coordinate, costo effettivo e costo euristica
; 5) direzione (che ha l'agente quando entra nella cella del nodo)
(deftemplate node (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot cost-real) (slot cost-heur) (slot direction))

(deftemplate frontier (slot path-id) (slot father-id) (slot node-r) (slot node-c) (slot cost-real) (slot cost-heur) (slot cost-total (default 0)) (slot direction))


(deftemplate generate-path-steps (slot path-id) (slot node-translate) 
	(slot action (allowed-values recount recount_last translate mirror clean) (default translate)) )


;(deftemplate obj-goal-pos (slot id) (slot pos-r) (slot pos-c) (slot solution-id) (slot intent) (slot type))
;(deftemplate candidate-goal-pos (slot father-obj-id) (slot id) (slot pos-r) (slot pos-c))
(deftemplate obj-pos (slot obj-id) (slot pos-r) (slot pos-c))
;(deftemplate goal-pos (slot father-obj-id) (slot id) (slot pos-r) (slot pos-c))
;
;(deftemplate path-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))

;id che viene assegnato agli obj-pos
(deftemplate obj-counter (slot id))		
;id che viene assegnato ai path
(deftemplate id-counter (slot id))

;TODO: meglio tenere l'id counter dei nodi univoci solo relativamente allo stesso path, quindi andrà riazzerato una volta finito di considerare un path
(deftemplate node-counter (slot id))

(deftemplate temp (slot count))

;//_______Functions



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
(defrule initialize_id_count 
	(declare (salience 15))
	(not (id-counter (id ?id)))
	=>
	(assert (id-counter (id 0)))
)

(defrule initialize_obj_count 
	(declare (salience 15))
	(not (obj-counter (id ?id)))
	=>
	(assert (obj-counter (id 0)))
)

(defrule initialize_node_count 
	(declare (salience 15))
	(not (node-counter (id ?id)))
	=>
	(assert (node-counter (id 0)))
)

(defrule initialize_path_obj_pos
	(declare (salience 13))
	(path-request (id ?ext-id) (from-r ?fr) (from-c ?fc) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
	(K-cell (pos-r ?tr) (pos-c ?tc))
	; ?e <- (obj-counter (id ?obj-id))
	; (not (obj-pos (pos-r ?tr) (pos-c ?tc)))
	=>
	(assert (obj-pos (obj-id ?ext-id) (pos-r ?tr) (pos-c ?tc)))
; 	(modify ?e (id (+ ?obj-id 1)))
 )

;(defrule initialize_path_to_empty
;	(declare (salience 10))
;	(path-request (id ?ext-id) (from-r ?fr) (from-c ?fc) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
;	(obj-pos (obj-id ?obj-id) (pos-r ?tr) (pos-c ?tc))
;	(K-cell (pos-r ?tr) (pos-c ?tc) (contains ?c))
;	?f <- (id-counter (id ?id))
;	(K-cell (pos-r ?r) (pos-c ?c) (contains Empty))
;	(test (or (and (= ?tr ?r) (= ?tc (+ ?c 1)))
;			  (and (= ?tr ?r) (= ?tc (- ?c 1)))
;			  (and (= ?tr (+ ?r 1)) (= ?tc ?c))
;			  (and (= ?tr (- ?r 1)) (= ?tc ?c))
;		)
;	)
;	=>
;	(if (eq ?c Empty) then  (assert (path (obj-id ?obj-id) (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) ))
;	else 	(assert (path (obj-id ?obj-id) (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?r) (to-c ?c) ))
;	(modify ?f (id (+ ?id 1)))
;	)
;)


(defrule initialize_path_to_empty
	(declare (salience 11))
	?g <- (path-request (id ?obj-id) (from-r ?fr) (from-c ?fc) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
	(obj-pos (obj-id ?obj-id) (pos-r ?tr) (pos-c ?tc))
	(K-cell (pos-r ?tr) (pos-c ?tc) (contains ?con))
	(test (or (eq ?con Empty) (eq ?con Robot) (eq ?con Parking)))
	?f <- (id-counter (id ?id))
	(not (path (obj-id ?obj-id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) ))
	=>
	(assert (path (obj-id ?obj-id) (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) ))
	(modify ?f (id (+ ?id 1)))
	;(retract ?g)
	
)

(defrule initialize_path_to_not_empty
	(declare (salience 11))
	?g <- (path-request (id ?obj-id) (from-r ?fr) (from-c ?fc) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
	(obj-pos (obj-id ?obj-id) (pos-r ?tr) (pos-c ?tc))
	(K-cell (pos-r ?tr) (pos-c ?tc) (contains ?cont))
	(test (neq ?cont Empty))
	?f <- (id-counter (id ?id))
	(K-cell (pos-r ?r) (pos-c ?c) (contains ?con))
	(test (or (and (= ?tr ?r) (= ?tc (+ ?c 1)))
			  (and (= ?tr ?r) (= ?tc (- ?c 1)))
			  (and (= ?tr (+ ?r 1)) (= ?tc ?c))
			  (and (= ?tr (- ?r 1)) (= ?tc ?c))
		)
	)
	(test (or (eq ?con Empty) (eq ?con Robot) (eq ?con Parking)))
	(not (path (obj-id ?obj-id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?r) (to-c ?c) ))
	=>
	(assert (path (obj-id ?obj-id) (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?r) (to-c ?c) ))
	(modify ?f (id (+ ?id 1)))
	;(retract ?g)
)

 

;inizializza la root del path per l'algoritmo A-STAR
(defrule A_star_root
	(declare (salience 10))
	(path (id ?id) (from-r ?fr) (from-c ?fc) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?ce) (solution no))
	?f <- (node-counter (id ?i))
	(test (= ?i 0))
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
	;considero anche suo padre, perché ho bisogno delle sue informazioni
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
	(not (node (path-id ?id) (node-r ?kr) (node-c ?kc)))
	=>
	(switch (turn ?dir (relative_direction ?nr ?nc ?kr ?kc)) 
	  (case same 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?kr) (node-c ?kc) (cost-real (+ ?cr 1)) (cost-heur (manhattan ?kr ?kc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) ) )
	  	) 
	  (case right 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?nr) (node-c ?nc) (cost-real (+ ?cr 2)) (cost-heur (manhattan ?nr ?nc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) )) 
	  	)	
	  (case left 
	  	then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?nr) (node-c ?nc) (cost-real (+ ?cr 2)) (cost-heur (manhattan ?nr ?nc ?tr ?tc)) (direction (relative_direction ?nr ?nc ?kr ?kc)) )) 
	  	)
	  (case opposite 
	  	then (switch ?dir 
	  		(case north then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?nr) (node-c ?nc) (cost-real (+ ?cr 2)) (cost-heur (manhattan ?nr ?nc ?tr ?tc)) (direction east) )))
	  		(case east then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?nr) (node-c ?nc) (cost-real (+ ?cr 2)) (cost-heur (manhattan ?nr ?nc ?tr ?tc)) (direction south) )))	  
	  		(case south then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?nr) (node-c ?nc) (cost-real (+ ?cr 2)) (cost-heur (manhattan ?nr ?nc ?tr ?tc)) (direction west) )))
	  		(case west then (assert (frontier (path-id ?id) (father-id ?i) (node-r ?nr) (node-c ?nc) (cost-real (+ ?cr 2)) (cost-heur (manhattan ?nr ?nc ?tr ?tc)) (direction north) ))) 
	 	     ) 
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
	?f <- (node-counter (id ?i))
	;considero un elemento della frontiera
	?e <-(frontier (path-id ?id) (father-id ?fid) (node-r ?nr) (node-c ?nc) (cost-real ?cr) (cost-total ?ct) (cost-heur ?ch) (direction ?dir))	
	(not (frontier (path-id ?id) (cost-total ?ct2&:(> ?ct ?ct2))))	
	;devo trovare quello con costo minimo....		
	=>
	(assert (node (path-id ?id) (node-id ?i) (father-id ?fid) (node-r ?nr) (node-c ?nc) (cost-real ?cr) (cost-heur ?ch)  (direction ?dir) ))
	(retract ?e)
	(modify ?f (id (+ ?i 1)))
)

(defrule A_star_terminate
	(declare (salience 10))	
	?f <- (path (id ?id) (start-dir ?sdir) (to-r ?tr) (to-c ?tc) (cost ?ce) (solution no))
	?e <- (node-counter)
	(node (path-id ?id) (node-id ?i) (father-id ?fid) (node-r ?tr) (node-c ?tc) (cost-real ?cr) (cost-heur ?ch) (direction ?dir))
	=>
	(modify ?f (solution yes) (cost ?cr))
	(modify ?e (id 0))
	(assert (generate-path-steps (path-id ?id) (node-translate ?i))	)
	)

(defrule generate_path_steps
	(declare (salience 12))
	(path (id ?id))
	?f <- (generate-path-steps (path-id ?id) (node-translate ?x) (action translate))
	(node (father-id ?fid) (node-id ?x) (path-id ?id) (node-r ?r) (node-c ?c) (direction ?dir))
	=>
	(assert (path-step (path-id ?id) (node-id ?x) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir)))
	(if (= ?fid ?x 0) 
		then (modify ?f (action recount))
			(assert (temp (count 0)))	
		else (modify ?f (node-translate ?fid))
	)
)

(defrule recount_path_steps
	(declare (salience 12))
	?v <- (temp (count ?var))
	(path (id ?id) (to-r ?tr) (to-c ?tc) )
	?f <- (generate-path-steps (path-id ?id) (node-translate ?x) (action recount))
	?e <- (path-step (path-id ?id) (node-id ?nid) (father-id ?var) )
	?g <- (path-step (path-id ?id) (node-id ?nid2) (father-id ?nid) )
	(test (not (and (= ?var 0) (= ?nid 0))))
	=>
	(modify ?e (node-id (+ ?var 1)))
	(modify ?g (father-id (+ ?var 1)))
	(modify ?v (count (+ ?var 1)))
)

(defrule recount_path_steps_last_leaf
	(declare (salience 13))
	?v <- (temp (count ?var))
	(path (id ?id))
	?f <- (generate-path-steps (path-id ?id) (node-translate ?x) (action recount))
	?e <- (path-step (path-id ?id) (node-id ?nid) (father-id ?var) )
	(not (path-step (path-id ?id) (node-id ?nid2) (father-id ?nid) ))
	
	=>
	(modify ?e (node-id (+ ?var 1)))
	(modify ?f (action clean))
	(retract ?v)
)


;alla fine di Astar, cancellare tutti i frontier
; tradurre i node in path-step
; cancellare i node

(defrule cleaning_nodes 	
	(declare (salience 12))
	(generate-path-steps (path-id ?id) (action clean))
	?f <- (node (path-id ?id)) 
	=>
	(retract ?f)
	
)

(defrule cleaning_frontier	
	(declare (salience 12))
	(generate-path-steps (path-id ?id) (action clean))
	?e <- (frontier (path-id ?id))
	=>
	(retract ?e)
)

(defrule cleaning_done	
	(declare (salience 12))
	?f <- (generate-path-steps (path-id ?id) (action clean))
	(not (node (path-id ?id)))
	(not (frontier (path-id ?id)))
	=>
	(retract ?f)
)

(defrule clean_request
	(declare (salience 2))
	?g <- (path-request (id ?obj-id) (from-r ?fr) (from-c ?fc) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
	=>
	(retract ?g)



	)

;TODO: La scelta del path migliore è ora di competenza di Strategy: riportare OGNI percorso.
;togliere
;(defrule choose_one_path
;	(declare (salience 4))
;	(K-agent (pos-r ?kr) (pos-c ?kc))
	;TODO: aggiungere un sistema di ID per le goal position
	; in modo da poter fare matching con i path id
;	?f <- (obj-goal-pos (id ?goalpos-id) (pos-r ?tr) (pos-c ?tc) (solution-id nil))
;	(path (obj-id ?gaolpos-id) (id ?id) (from-r ?kr) (from-c ?kc) (start-dir ?sdir) (cost ?c) (solution yes))
;	(not (path (obj-id ?gaolpos-id) (from-r ?kr) (from-c ?kc) (start-dir ?sdir) (cost ?c2&:(< ?c2 ?c)) (solution yes)))
;	=>
;	(modify ?f (solution-id ?id))
;	(pop-focus)
;)