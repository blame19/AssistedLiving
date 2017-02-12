
;// ACTION

(defmodule ACTION (import MAIN ?ALL) (export ?ALL) (import AGENT ?ALL) (import STRATEGY ?ALL))



;//_______Facts
(deftemplate translate_path (slot id))
(deftemplate current-step-counter (slot step))
(deftemplate node-counter (slot i))

(deftemplate copy-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))
(deftemplate number-of-steps (slot number))

;//_______Rules

(defrule read_todo_initialize
	(declare (salience 15))
	(exec-todo (id ?id))
	(todo (id ?id) (chosen_path ?path-id) (step ?s) (sender ?P) (request ?req))	
	=>
	(assert (translate_path (id ?path-id)))
	(assert (node-counter (i 0)))
	(assert (current-step-counter (step 0)))
)

(defrule current_step_initialize
	(declare (salience 15))
	(K-agent (step ?step))
	?f <- (current-step-counter (step ?step2))
	(test (< ?step2 ?step))
	=>
	(modify ?f (step ?step))

	)

(defrule copy-path-steps
	(declare (salience 13))
	(translate_path (id ?path-id))	
	(path-step (path-id ?path-id) (node-id ?nid) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir))
	=>
	(assert (copy-step (path-id ?path-id) (node-id ?nid) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir)))
)

(defrule count-path-steps
	(declare (salience 13))
	(translate_path (id ?path-id))	
	(path-step (path-id ?path-id) (node-id ?nid) (father-id ?fid) (node-r ?r) (node-c ?c) (direction ?dir))
	(not (path-step (path-id ?path-id) (node-id ?nid2&:(> ?nid2 ?nid))))
	=>
	(assert (number-of-steps (number ?nid)))
)

; (defrule exec-preliminary-action
; 	(declare (salience 10))
; 	(exec-todo (id ?id))
; 	?g <- (current-step-counter (step ?step))
; 	(todo (id ?id) (chosen_path ?path-id) (step ?s) (sender ?P) (request ?req))
; 	=>
; 	(if (eq ?req load_meal)
; 		then (assert (proto-exec (step ?step) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))
;         	     (modify ?g (step (+ ?step 1)))
;     	)
; )


;Se è stato scelto un todo di tipo load_meal o load_dessert, l'agente deve anche effettuare l'inform necessario
(defrule inform_yes
      (declare (salience 14))
      (exec-todo (id ?id))
      ?g <- (current-step-counter (step ?step))
      ?f <- (todo (id ?id) (chosen_path ?path-id) (sender ?P) (request ?req) (informed ?info))
      (test (or (eq ?info no) (eq ?info wait)))
      (test (or (eq ?req load_meal) (eq ?req load_dessert)))
      =>
      (if (eq ?req load_meal)
              then (assert (proto-exec (todo-id ?id) (step ?step) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))
                   (modify ?f (informed yes))
                   (modify ?g (step (+ ?step 1)))
        )
      (if (eq ?req load_dessert)
              then (assert (proto-exec (todo-id ?id) (step ?step) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil)))
                   (modify ?f (informed yes))
                   (modify ?g (step (+ ?step 1)))
        )
)


;Se è stato scelto un todo di un certo tipo, ma esiste anche un altro todo in attesa di tipo load_meal o dessert per qualcuno,
;quella persona viene fatta attendere
(defrule inform_delay
      (declare (salience 14))
      (exec-todo (id ?id))
      ?g <- (current-step-counter (step ?step))
      (todo (id ?id) (chosen_path ?path-id) (sender ?P) (request ?req) (informed yes))
      ?f <- (todo (id ?id2&:(neq ?id ?id2)) (sender ?P2) (request ?req2) (informed no))
      (test (or (eq ?req2 load_meal) (eq ?req2 load_dessert)))
      =>
      (if (eq ?req2 load_meal)
              then (assert (proto-exec (todo-id ?id) (step ?step) (action Inform) (param1 ?P2) (param2 meal) (param3 wait) (param4 nil)))
                   (modify ?f (informed wait))
                   (modify ?g (step (+ ?step 1)))                  
        )
      (if (eq ?req2 load_dessert)
              then (assert (proto-exec (todo-id ?id) (step ?step) (action Inform) (param1 ?P2) (param2 dessert) (param3 wait) (param4 nil)))
                   (modify ?f (informed wait))
                   (modify ?g (step (+ ?step 1)))                       
        )
)


(defrule exec-path
	(declare (salience 10))
	(translate_path (id ?path-id))
        ;(K-agent (step ?step) (pos-r ?r) (pos-c ?c) (direction ?sdir))
        ?f <- (node-counter (i ?i))
        ?g <- (current-step-counter (step ?step))
        (copy-step (path-id ?path-id) (node-id ?i) (father-id ?fid) (node-r ?r1) (node-c ?c1) (direction ?dir1))
        (copy-step (path-id ?path-id) (node-id ?y) (father-id ?i) (node-r ?r2) (node-c ?c2) (direction ?dir2))
        (test (neq ?i ?y))
        (number-of-steps (number ?max))
        (test (< ?i ?max))
        (exec-todo (id ?id))
        =>
        (if (and (eq ?r1 ?r2) (eq ?c1 ?c2))
        	then ;TURN ROBOT
        		(switch (turn ?dir1 ?dir2)
        			(case left then 
        				(assert (proto-exec (todo-id ?id) (step ?step) (action Turnleft)))
        				(modify ?g (step (+ ?step 1))))
        			(case right then 
        				(assert (proto-exec (todo-id ?id) (step ?step) (action Turnright)))
        				(modify ?g (step (+ ?step 1))))
        		)
        	else ;GO FORWARD
        		(assert (proto-exec (todo-id ?id) (step ?step) (action Forward)))
        		(modify ?g (step (+ ?step 1)))

        	)
        (modify ?f (i (+ ?i 1)))
)

;All'ultimo passo del percorso l'agente ha raggiunto la posizione di goal (goal_pos)
;può quindi eseguire l'azione che voleva fare, indicata dalla ?req nel todo
(defrule exec-path-last-step
	(declare (salience 10))
	?h <- (translate_path (id ?path-id))
        ;(K-agent (step ?step) (pos-r ?r) (pos-c ?c) (direction ?sdir))
        ?f <- (node-counter (i ?i))
        ?g <- (current-step-counter (step ?step))        
        (number-of-steps (number ?max))
        (test (= ?i ?max))

        ?k <- (exec-todo (id ?id))
	?l <- (todo (id ?id) (chosen_path ?path-id) (step ?s) (sender ?P) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc))
	(prescription (patient ?P) (meal ?type) (pills ?pills))

        (copy-step (path-id ?path-id) (node-id ?i) (father-id ?fid) (node-r ?r1) (node-c ?c1) (direction ?dir1))
        ;(not (copy-step (path-id ?path-id) (node-id ?y&:(> ?y ?i)) (father-id ?i)))        
        =>
        (switch ?req 
        	(case load_meal then (assert (proto-exec (todo-id ?id) (step ?step) (action LoadMeal) (param1 ?gr) (param2 ?gc) (param3 ?type) (last-action yes) ))
        				(modify ?g (step (+ ?step 1))))
        	(case meal then (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryMeal) (param1 ?gr) (param2 ?gc) (param3 ?type) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case load_dessert then (assert (proto-exec (todo-id ?id) (step ?step) (action LoadDessert) (param1 ?gr) (param2 ?gc) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case dessert then (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryDessert) (param1 ?gr) (param2 ?gc) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case load_pills then (assert (proto-exec (todo-id ?id) (step ?step) (action LoadPill) (param1 ?gr) (param2 ?gc) (param3 ?P) (last-action yes)))
        				(modify ?g (step (+ ?step 1))))
        	(case meal_before then  (assert (proto-exec (todo-id ?id) (step ?step) (action DeliveryPill) (param1 ?gr) (param2 ?gc) (param3 ?P)))
        				(assert (proto-exec (todo-id ?id) (step (+ ?step 1)) (action DeliveryMeal) (param1 ?gr) (param2 ?gc) (param3 ?type) (last-action yes)))
        				(modify ?g (step (+ ?step 2))))
        )
        (retract ?h)
        (retract ?k)
        ;(retract ?l)
        (focus AGENT)
)



;// ACTION_OLD

(defmodule ACTION_OLD (import MAIN ?ALL) (export ?ALL) (import AGENT ?ALL) (import STRATEGY ?ALL))



;//_______Facts

(deftemplate id-goal-pos (slot id))

(deftemplate get-meal (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot type))
(deftemplate get-dessert (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot type))
(deftemplate get-pills (slot step) (slot sender) (slot t_pos-r) (slot t_pos-c) (slot when))


(deftemplate obj-goal-pos (slot id) (slot pos-r) (slot pos-c) (slot solution-id) (slot intent) (slot type))
(deftemplate candidate-goal-pos (slot father-obj-id) (slot id) (slot pos-r) (slot pos-c))
(deftemplate goal-pos (slot id) (slot pos-r) (slot pos-c))

;(deftemplate path-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))
(deftemplate current-step (slot value))
;Va aggiunta una qualche sorta di lista delle azioni da mandare in exec (da gestire tramite gli "step" numerici)

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
	(assert (current-step (value 1)))
)


;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=meal, e l'agente passa il focus
(defrule rcv_msg_meal
	;forse è necessario ritrattare il fatto msg-to-agent
	?g <- (msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(K-agent (free ?free) (waste ?waste))	
	(prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
	?e <- (current-step (value ?v))
	=>
	;1 answer the request
	(assert (proto-exec (step ?v) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	(modify ?e (value (+ ?v 1)))
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
	(retract ?g)	
)

;Si attiva quando viene ricevuto un messaggio dall'agente di tipo request=dessert, e l'agente passa il focus
(defrule rcv_msg_dessert
	(msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	?f <- (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc) (taken no))
	?e <- (current-step (value ?v))

	=>
	;1 answer the request
	(assert (proto-exec (step ?v) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil)))	
	(modify ?f (taken yes))
	(modify ?e (value (+ ?v 1)))
	;2 plan how to get the dessert
)


;Si attiva quando esiste un fatto di tipo get-meal e quindi bisogna pianificare
;Il percorso fino al meal dispenser e il carico
;bisogna ricordare che questa regola si attiva quando è già stata mandata un'exec di tipo Inform per accettare la richiesta di pasto
;di conseguenza se vengono lanciate ulteriori exec devono avere step maggiore di quello dell'inform (vedi regola rcv_msg_meal)
(defrule get_to_meal_disp 
	?g <- (get-meal (step ?s) (sender ?P) (t_pos-r ?tr) (t_pos-c ?tc) (type ?type))
	(K-agent (step ?sA) (time ?sT) (pos-r ?rA) (pos-c ?cA) (direction ?dir) (free ?fr) (waste ?w))
	(K-cell (pos-r ?rdisp) (pos-c ?cdisp) (contains MealDispenser))
	?e <- (id-goal-pos (id ?id))
	?f <- (current-step (value ?v))
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
			(assert (proto-exec (step ?v) (action LoadMeal) (param1 ?rdisp) (param2 ?cdisp) (param3 ?type)))
			(modify ?f (value (+ ?v 1)))
			;Qui si possono fare due cose :
			; 1 Lasciare il comando all'agente, fargli prendere il carico, e vedere se nel frattempo arrivano altre richieste
			;    ricordando che la LoadMeal impiega 15 unità di tempo, potrebbe essere conveniente
			;	(pop focus)
			; 2 Passare al planning del percorso per il tavolo ?tr ?tc
			 (assert (obj-goal-pos (id ?id) (pos-r ?tr) (pos-c ?tc) (intent Meal) (type ?type)))
			 (modify ?e (id (+ ?id 1)))
			 (retract ?g)			 
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


;Trasforma il path calcolato dal modulo apposito in fatti di tipo proto-exec
;che l'agente può attuare e manipolare passo passo
;TODO inibire e trasportare su strategy
;(defrule exec_path
;	;salience??
;	(declare (salience 12))	
;	(K-agent (step ?step) (pos-r ?kr) (pos-c ?kc) (direction ?kdir) )
;	(obj-goal-pos (id ?obj-id) (solution-id ?solution-id))	
;	(path-step (path-id ?solution-id) (node-id ?x) (node-r ?kr) (node-c ?kc))
;	;nodo figlio. il prossimo da raggiungere nel path
;	(path-step (path-id ?solution-id) (node-id ?y) (father-id ?x) (node-r ?sonr) (node-c ?sonc) (direction ?sondir))
;	?f <- (current-step (value ?value))
;	(test (neq ?y ?x))
;	=>
;	(switch (turn ?kdir ?sondir) 
;		(case same then (assert (proto-exec (step (+ ?value 0)) (action Forward))) 
;				
;		(modify ?f (value (+ ?value 1)))
;		)
;
;		(case left then (assert (proto-exec (step (+ ?value 0)) (action Turnleft))
;					(proto-exec (step (+ ?value 1)) (action Forward))) 
;						(modify ?f (value (+ ?value 2)))
;					
;
;		)
;
;		(case right then (assert (proto-exec (step (+ ?value 0)) (action Turnright))
;					(proto-exec (step (+ ?value 1)) (action Forward)) )
;							(modify ?f (value (+ ?value 2)))
					
;				)
;
;		(case opposite then (assert (proto-exec (step (+ ?value 0)) (action Turnleft))
;					    (proto-exec (step (+ ?value 1)) (action Turnleft))
;					    (proto-exec (step (+ ?value 2)) (action Forward)))
;							(modify ?f (value (+ ?value 3))) 
				

;		)	

;	)
;	(pop-focus)		
;)


(defrule exec_intent
	(declare (salience 12)) 
	?e <- (obj-goal-pos (id ?obj-id) (pos-r ?objr) (pos-c ?objc) (solution-id ?solution-id) (intent ?intent) (type ?type))	
	(K-agent (step ?step) (pos-r ?kr) (pos-c ?kc) (direction ?kdir) )
	;l'agente è al path-step x
	(path-step (path-id ?solution-id) (node-id ?x) (node-r ?kr) (node-c ?kc))
	; e non esiste un path step con id maggiore: quindi ha raggiunto l'obbiettivo
	(not (path-step (path-id ?solution-id) (node-id ?y&:(> ?y ?x))))
	?f <- (current-step (value ?value))
	=>
	(switch ?intent 
		(case Meal then (assert (proto-exec (step (+ ?value 0)) (action DeliveryMeal) (param1 ?objr) (param2 ?objc) (param3 ?type) ) ))
		(case Pills then (assert (proto-exec (step (+ ?value 0)) (action DeliveryDessert) (param1 ?objr) (param2 ?objc) ) ))			
		(case Dessert then (assert (proto-exec (step (+ ?value 0)) (action DeliveryPills) (param1 ?objr) (param2 ?objc) ) ))
	)
	(retract ?e)
	(pop-focus)


)

;(defrule is_there_proto-exec
;	(declare (salience 12))
;	(K-agent (step ?step) (pos-r ?kr) (pos-c ?kc) (direction ?kdir) )
;	(proto-exec (step ?step))
;	=>
;	(pop-focus)

;	)