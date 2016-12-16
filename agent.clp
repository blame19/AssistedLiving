;// AGENT


(defmodule AGENT (import MAIN ?ALL) (export ?ALL))

;(defglobal ?*id-goal-pos* = 0 )


;//_______Templates
(deftemplate K-cell  (slot pos-r) (slot pos-c) (slot contains))

(deftemplate K-agent
	(slot step)
	(slot time) 
	(slot pos-r) 
	(slot pos-c) 
	(slot direction) 
	(multislot content)
	(slot free)
    (slot waste)
)

(deftemplate K-received-msg 
	(slot step)
	(slot sender)
	(slot request)
	(slot t_pos-r)
	(slot t_pos-c)	
	;slot per indicare se l'agente si è preso carico della richiesta
	(slot taken (allowed-values yes no))
	;slot per indicare se la richiesta è stata portata a termine dall'agente
	(slot completed (allowed-values yes no) (default no))
)


;(deftemplate goal-pos (slot id) (slot pos-r) (slot pos-c))
;(deftemplate goal-achieve (slot status))
;(deftemplate path-to-goal (slot id) (slot pos-r) (slot pos-c) (slot direction))
;(deftemplate go-direction (slot step) (slot direction))

;//_______Functions

; Funzione che restituisce "come muoversi" o "dove girarsi" per passare da una direzione
; all'altra. Dir1 è in genere la direzione dell'agente, dir2 quella desiderata. 
; restituisce left, right, same (se si è già allineati) e opposite (se le due direzioni sono opposte e non ha importanza dove girarsi)
(deffunction turn (?dir1 ?dir2) 
	(switch ?dir1
		(case north then 
			(switch ?dir2
				(case north then same)
				(case south then opposite)
				(case west then left)
				(case east then right)
			) 
		)
		(case south then
			(switch ?dir2
				(case north then opposite)
				(case south then same)
				(case west then right)
				(case east then left)
			) 
		)
		(case west then 
			(switch ?dir2
				(case north then right)
				(case south then left)
				(case west then same)
				(case east then opposite)
			) 
		)
		(case east then 
			(switch ?dir2
				(case north then left)
				(case south then right)
				(case west then opposite)
				(case east then same)
			) 
		)
	)
)

;//_______Rules

(defrule  beginagent1
    (declare (salience 11))
    (status (step 0))
    (not (exec (step 0)))
    (prior-cell (pos-r ?r) (pos-c ?c) (contains ?x)) 
	=>
	(assert (K-cell (pos-r ?r) (pos-c ?c) (contains ?x)))
)

(defrule  beginagent2
      (declare (salience 10))
      (status (step 0))
      (not (exec (step 0)))
      (K-cell (pos-r ?r) (pos-c ?c) (contains Parking))  
	  =>
     (assert (K-agent (time 0) (step 0) (pos-r ?r) (pos-c ?c) (direction north) (free 2) (waste no)))
	 ;linee aggiunte rispetto al codice originale, per provare il cammino verso un goal
	 ;(assert (goal-pos (id 1) (pos-r 2) (pos-c 2)))
	 ;(assert (goal-achieve (status false)))
)

;Regola che si attiva all'arrivo di una richiesta di meal.
;Delega al planner la gestione della richiesta
;Salva inoltre una copia della richiesta in K-received-msg: la memoria dell'agente sui messaggi passati
(defrule on_meal_req_received
	(declare (salience 10))
	(msg-to-agent (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
	(status (step ?i))
	(test (= ?s ?i))
	(not (K-received-msg (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)))
	(focus PLANNER)
)

;Regola che si attiva all'arrivo di una richiesta di dessert.
;Delega al planner la gestione della richiesta SE:
; 1) è previsto che il paziente possa avere il dessert
; 2) TODO: all'agente risulta che il paziente abbia già consumato il meal 
;Salva inoltre una copia della richiesta in K-received-msg: la memoria dell'agente sui messaggi passati
(defrule on_dessert_req_received
	(declare (salience 10))
	(msg-to-agent (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (pills ?pills) (dessert ?dessert))
	;(consumed-meal (patient ?P)) condizione da aggiungere: se un paziente ha finito di mangiare il suo pranzo, riceve il dessert
	(status (step ?i))
	(test (= ?s ?i))	
	(not (K-received-msg (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>
	(if (neq ?dessert yes) then
		;Rifiuto della richiesta perché contraria alla prescrizione 
		(assert (exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 rejected) (param4 nil)))
		else 
		(focus PLANNER)
	)		
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
)
	
; Ho stabilito che al primo step l'azione sia una wait, per avere le percezioni	
(defrule ask_act_0	
 ?f <-   (status (step 0))
    =>  (printout t crlf crlf)
        (printout t "first action: wait to get perceptions")
        (printout t crlf crlf)
        (modify ?f (work on))		
		(assert (exec (step 0) (action Wait)))			
)

; Fa l'update del fatto K-agent in base alle percezioni ricevute e ritira quello dello step precedente
(defrule update_agent 
	(declare (salience 12))
	(perc-vision (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d))
	?f <- (K-agent (step ?sA) (free ?fr) (waste ?w))
	(test (< ?sA ?s))
	=>
	(modify ?f (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d) (free ?fr) (waste ?w))
)	

	
(defrule ask_act
 ?f <-   (status (step ?i))
 (not (status (step 0)))
    =>  (printout t crlf crlf)
        (printout t "action to be executed at step:" ?i)
        (printout t crlf crlf)
        (modify ?f (work on))			
)
		
(defrule exec_act
    (status (step ?i))
    (exec (step ?i))
 => (focus MAIN)
)

;(defrule goal_pos_achieved 
;	(declare (salience 10))
;	(goal-pos (id ?i) (pos-r ?x) (pos-c ?y))
;	(K-agent (pos-r ?x) (pos-c ?y))
;	=>
;	(assert (goal-achieve (status true)))
;	(printout t "goal achieved, good job")
;)

; A seconda di goal-pos, asserisce fatti di tipo "go-direction" per capire in che direzione deve andare
;(defrule get_direction
;	(declare (salience 9))
;	(goal-pos (pos-r ?x) (pos-c ?y))
;	(K-agent (step ?s) (pos-r ?r) (pos-c ?c))
;	=>
;	(if (> ?x ?r)
;		then (assert (go-direction (step ?s) (direction north))) )
;	(if (> ?r ?x)
;		then (assert (go-direction (step ?s) (direction south))))
;	(if (> ?c ?y) 
;		then (assert (go-direction (step ?s) (direction west))))
;	(if (> ?y ?c) 
;		then (assert (go-direction (step ?s) (direction east))))
;)

; Questa regola cerca delle K-cell vuote che siano nella stessa direzione di go-direction
; Manca una strategia di risoluzione dei conflitti. Se l'agente si trova davanti un "muro" rispetto alla direzione
; in cui vuole andare, non vengono generati "path-to-goal" e non ci si muove più
; metodo greedy
;(defrule get_path_to_goal 
;	(declare (salience 8))
;	(goal-pos (id ?i) (pos-r ?x) (pos-c ?y))
;	(K-agent (pos-r ?rA) (pos-c ?cA))
;	(K-cell (pos-r ?r1) (pos-c ?c1) (contains Empty))
;	(go-direction (direction ?where))
;	(test (or 
;			(and (= ?r1 (- ?rA 1)) (= ?c1 ?cA) (not(neq ?where south)))
;			(and (= ?r1 (+ ?rA 1)) (= ?c1 ?cA) (not(neq ?where north)))
;			(and (= ?c1 (- ?cA 1)) (= ?r1 ?rA) (not(neq ?where west)))
;			(and (= ?c1 (+ ?cA 1)) (= ?r1 ?rA) (not(neq ?where east)))
;	))
;	=>
;	(printout t "found something")
;	(printout t crlf crlf)
;	(assert (path-to-goal (id ?i) (pos-r ?r1) (pos-c ?c1) (direction ?where)))
;)
;
;(defrule dead_ends
;	(declare (salience 8))
;	(goal-pos (id ?i) (pos-r ?x) (pos-c ?y))
;	(K-agent (pos-r ?rA) (pos-c ?cA))
;	(go-direction (direction ?where))
;	(K-cell (pos-r ?r1) (pos-c ?c1) (contains (neq Empty)))
;	(test (or 
;			(and (= ?r1 (- ?rA 1)) (= ?c1 ?cA) (not(neq ?where south)))
;			(and (= ?r1 (+ ?rA 1)) (= ?c1 ?cA) (not(neq ?where north)))
;			(and (= ?c1 (- ?cA 1)) (= ?r1 ?rA) (not(neq ?where west)))
;			(and (= ?c1 (+ ?cA 1)) (= ?r1 ?rA) (not(neq ?where east)))
;	))
;	=>
;	(printout t "found a dead end, must go back")
;	(printout t crlf crlf)
;	(assert (dead_end (id ?i) (pos-r ?rA) (pos-c ?cA) (direction ?where)))
;)		
		
; Regola che cerca di direzionare l'agente verso il path-to-goal precedentemente deciso
; da riscrivere		
;(defrule get_to_path 
;	(declare (salience 7))
;	(status (step ?s))
;	?f <-(path-to-goal (id ?i) (pos-r ?r1) (pos-c ?c1) (direction ?d))
;	(K-agent (direction ?dA))	
	;quest'ultima clausola impedisce che la regola si attivi se è già presente un'exec
	;di fatto viene eseguita solo la prima exec generata, e non la migliore. Problema
;	(not (exec (step ?s)))
;	=>
;	(switch (turn ?dA ?d)
;		(case same then 
;			(assert (exec (step ?s) (action Forward)))
;			;(printout t "go on " ?s)
;		)
;		(case right then 
;			(assert (exec (step ?s) (action Turnright)))
;			;(printout t "turn Right " ?s)
;		)
;		(case left then 
;			(assert (exec (step ?s) (action Turnleft)))
;			;(printout t "turn Left" ?s)
;		)
;		(case opposite then 
;			(assert (exec (step ?s) (action Turnleft)))
;			;(printout t "turn Left" ?s)
;		)		
;	)
;	(printout t crlf crlf)
;	(retract ?f)	
;)		

;(defrule update_cells 
;	(declare (salience 11))
;	(perc-vision (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d))
;	(status (step ?s1))	
;	?f <-(K-cell (pos-r ?r1) (pos-c ?c1) (contains ?x))
	;Il test seleziona solo le k-cell che siano nel quadrato attorno alla posizione del robot
;	(test (or			
;			(and (= ?r1 (- ?r 1)) (= ?c1 (+ ?c 1)))
;			(and (= ?r1 (- ?r 1)) (= ?c1 ?c))
;			(and (= ?r1 (- ?r 1)) (= ?c1 (- ?c 1)))
;			(and (= ?r1 ?r) (= ?c1 (+ ?c 1)))
;			(and (= ?r1 ?r) (= ?c1 ?c))
;			(and (= ?r1 ?r) (= ?c1 (- ?c 1)))
;			(and (= ?r1 (- ?r 1)) (= ?c1 (+ ?c 1)))
;			(and (= ?r1 (- ?r 1)) (= ?c1 ?c))			
;			(and (= ?r1 (- ?r 1)) (= ?c1 (- ?c 1)))
;			)
	;il test serve a essere sicuri di prendere la perc-vision attuale (l'ultima registrata)		
;	(test (= ?s1 ?s))
;	=>		
;	(assert )	
;)

; Ritira i fatti go-direction dello step precedente
;(defrule retract_prev_directions 
;	(declare (salience 11))	
;	(perc-vision (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d))
;	?f <- (go-direction (step ?sgd) (direction ?any))	
;	(test (< ?sgd ?s))
;	=>
;	(retract ?f)
;)
	