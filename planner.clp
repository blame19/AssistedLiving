;// PLANNER

(defmodule PLANNER (import MAIN ?ALL) (export ?ALL) (import AGENT ?ALL))



;//_______Facts

(deftemplate id-goal-pos (slot id))

(deftemplate get-meal (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot type))
(deftemplate get-pills (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot when))


(deftemplate obj-goal-pos (slot id) (slot pos-r) (slot pos-c) (slot solution-id))
(deftemplate candidate-goal-pos (slot father-obj-id) (slot id) (slot pos-r) (slot pos-c))
(deftemplate goal-pos (slot id) (slot pos-r) (slot pos-c))

(deftemplate path-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))
(deftemplate current-step (slot value))
;Va aggiunta una qualche sorta di lista delle azioni da mandare in exec (da gestire tramite gli "step" numerici)

;//_______Functions

;//_______Rules

(defrule initialize_id 
	(declare (salience 15))
	(not (id-goal-pos (id ?id)))
	=>
	(assert (id-goal-pos (id 0)))
)

(defrule initialize_current_step
	(declare (salience 15))
	(not (current-step (value ?v)))
	=>
	(assert (current-step (value 0)))
)


;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=meal, e l'agente passa il focus
(defrule rcv_msg_meal
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(K-agent (free ?free) (waste ?waste))	
	(prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
	=>
	;1 answer the request
	(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	;2 plan how to get the meal
	(if (neq ?pills no) then 
		(if (and (> ?free 1) (neq ?waste yes)) 
			then (printout t "must get meal and pills")
				(assert (get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?meal)))
				(assert (get-pills (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (when ?pills)))						
			else (printout t "must make room")
				;TODO : gestire lo spazio
		)
		
	else (if (and (> ?free 0) (neq ?waste yes)) 
		then (printout t "must get meal")
			(assert (get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?meal)))			
		else (printout t "must make room")
		;TODO : gestire lo spazio
		)
	)		
	
)

;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=dessert, e l'agente passa il focus
(defrule rcv_msg_dessert
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	=>
	;1 answer the request
	(assert (proto-exec (step (+ ?s 1))) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil))	
	(modify ?f (taken yes))
	;2 plan how to get the dessert
)


;Si attiva quando esiste un fatto di tipo get-meal e quindi bisogna pianificare
;Il percorso fino al meal dispenser e il carico
;bisogna ricordare che questa regola si attiva quando è già stata mandata un'exec di tipo Inform per accettare la richiesta di pasto
;di conseguenza se vengono lanciate ulteriori exec devono avere step maggiore di quello dell'inform (vedi regola rcv_msg_meal)
(defrule get_to_meal_disp 
	(get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?type))
	(K-agent (step ?sA) (time ?sT) (pos-r ?rA) (pos-c ?cA) (direction ?dir) (free ?fr) (waste ?w))
	(K-cell (pos-r ?rdisp) (pos-c ?cdisp) (contains MealDispenser))
	?e <- (id-goal-pos (id ?id))
	=>	
	;Controllo se l'agente è su uno dei quattro accessi al dispenser	
	(if 
		(or  
			(and (= ?rdisp ?rA) (= ?cdisp (+ ?cA 1)) )
			(and (= ?rdisp ?rA) (= ?cdisp (- ?cA 1)) )
			(and (= ?rdisp (+ ?rA 1)) (= ?cdisp ?cA ))
			(and (= ?rdisp (- ?rA 1)) (= ?cdisp ?cA))
		) 
		then
			(assert (proto-exec (step (+ ?s 1)) (action LoadMeal) (param1 ?rdisp) (param2 ?cdisp) (param3 ?type)))
			;Qui si possono fare due cose :
			; 1 Lasciare il comando all'agente, fargli prendere il carico, e vedere se nel frattempo arrivano altre richieste
			;    ricordando che la LoadMeal impiega 15 unità di tempo, potrebbe essere conveniente
			;	(pop focus)
			; 2 Passare al planning del percorso per il tavolo ?tr ?tc
			 (assert (obj-goal-pos (id ?id) (pos-r ?tr) (pos-c ?tc)))
			 (modify ?e (id (+ ?id 1)))			 
	else 
		;TODO: raggiungi il meal dispenser
		(printout t "dove?" clrf)
	)	
)

;regola per capire quali celle libere ci sono attorno a un tavolo o a un dispenser
;fa il calcolo basandosi sulla conoscenza dell'agente
;genera dei "candidati" a posizione di goal, che devono essere poi usati per calcolare un percorso ottimale
(defrule goal_near_object 
	(declare (salience 10))
	?f <- (obj-goal-pos (id ?x) (pos-r ?tr) (pos-c ?tc) (solution-id nil))
	(K-cell (pos-r ?r) (pos-c ?c) (contains Empty))
	(test (or (and (= ?tr ?r) (= ?tc (+ ?c 1)))
			  (and (= ?tr ?r) (= ?tc (- ?c 1)))
			  (and (= ?tr (+ ?r 1)) (= ?tc ?c))
			  (and (= ?tr (- ?r 1)) (= ?tc ?c))
		)
	)
	?e <- (id-goal-pos (id ?id))
	(not (candidate-goal-pos (pos-r ?r) (pos-c ?c)))
	=> 
	(assert (candidate-goal-pos (father-obj-id ?x) (id ?id) (pos-r ?r) (pos-c ?c)))
	(modify ?e (id (+ ?id 1)))	
)

(defrule ask_to_module_path
	(declare (salience 9))
	(candidate-goal-pos (pos-r ?r) (pos-c ?c))
	=> 
	(focus PATH)
)


(defrule define_next_step_1
	(declare (salience 14))	
	(proto-exec (step ?st))
	(not (proto-exec (step ?st2&:(> ?st2 ?st))))
	?f <- (current-step (value ?v))
	(test (not (= ?st ?v)))	
	=>
	(modify ?f (value ?st)))
)

(defrule define_next_step_2
	(declare (salience 14))	
	(K-agent (step ?step))	
	(not (proto-exec (step ?i)))
	?f <- (current-step (value ?v))
	(test (not (= ?v ?step)))		
	=>
	(modify ?f (value ?step))
)

(defrule exec_path
	;salience??
	(declare (salience 12))
	
	(K-agent (step ?step) (pos-r ?kr) (pos-c ?kc) (direction ?kdir) )
	(obj-goal-pos (id ?obj-id) (solution-id ?solution-id))	
	(path-step (path-id ?solution-id) (node-id ?x) (node-r ?kr) (node-c ?kc))
	;nodo figlio. il prossimo da raggiungere nel path
	(path-step (path-id ?solution-id) (node-id ?y) (father-id ?x) (node-r ?sonr) (node-c ?sonc) (direction ?sondir))
	(current-step (value ?value))
	(test (neq ?y ?x))
	=>
	(switch (turn ?kdir ?sondir) 
		(case same then (assert (proto-exec (step (+ ?value 1)) (action Forward))) 
				)

		(case left then (assert (proto-exec (step (+ ?value 1)) (action Turnleft))
					(proto-exec (step (+ ?value 2)) (action Forward)) )
					

		)

		(case right then (assert (proto-exec (step (+ ?value 1)) (action Turnright))
					(proto-exec (step (+ ?value 2)) (action Forward))
						 )
					
				)

		(case opposite then (assert (proto-exec (step (+ ?value 1)) (action Turnleft))
					    (proto-exec (step (+ ?value 2)) (action Turnleft))
					    (proto-exec (step (+ ?value 3)) (action Forward))
						 )
				

		)	

	)
	(pop-focus)
		
)

;(defrule is_there_proto-exec
;	(declare (salience 12))
;	(K-agent (step ?step) (pos-r ?kr) (pos-c ?kc) (direction ?kdir) )
;	(proto-exec (step ?step))
;	=>
;	(pop-focus)

;	)