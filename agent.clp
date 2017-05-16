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
    (slot penalty)
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

(deftemplate K-table
	(slot t_pos-r)
	(slot t_pos-c)
	(slot clean (allowed-values yes no))
	(slot meal_delivered_at_time)
	(slot meal_delivered_at_person)
)

(deftemplate K-pill-delivered
	(slot person)
)

(deftemplate proto-exec (slot todo-id) (slot step) (slot action) (slot param1) (slot param2) (slot param3) (slot param4) (slot last-action (default no)))

(deftemplate K-exec (slot step) (slot action) (slot param1) (slot param2) (slot param3) (slot param4))
(deftemplate executed-todo (slot todo-id))

(deftemplate max_duration (slot time))
(deftemplate bump-avoid (slot todo-id) (slot step) (slot pos-r) (slot pos-c) (slot intent))
(deftemplate proto-exec-reorder (slot reorder-step))

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

(deffunction manhattan (?r1 ?c1 ?r2 ?c2)
	(if (or (= (- ?r1 ?r2) 0) (= (- ?c1 ?c2) 0)) 
		then (+ (abs(- ?r1 ?r2)) (abs(- ?c1 ?c2)))

		else (+ (abs(- ?r1 ?r2)) (abs(- ?c1 ?c2)) 2) 
	)
)

;//_______Rules

(defrule  beginagent_1
    (declare (salience 11))
    (status (step 0))
    (not (exec (step 0)))
    (prior-cell (pos-r ?r) (pos-c ?c) (contains ?x)) 
	=>
	(assert (K-cell (pos-r ?r) (pos-c ?c) (contains ?x)))
	(if (eq ?x Table) 
		then 
		(assert (K-table (t_pos-r ?r) (t_pos-c ?c) (clean yes)) )
	)
)

(defrule  beginagent_2
      (declare (salience 10))
      (status (step 0))
      (not (exec (step 0)))
      (maxduration ?d)
      (K-cell (pos-r ?r) (pos-c ?c) (contains Parking))  
      =>
      (assert (K-agent (time 0) (step 0) (pos-r ?r) (pos-c ?c) (content Empty) (direction north) (free 2) (waste no) (penalty 0)))
      (assert (max_duration (time ?d)))	
)

;Regola che si attiva all'arrivo di una richiesta di meal.
;Manda subito l'inform, poi strategy si occuperà di come e quando portarla a termine
;Salva inoltre una copia della richiesta in K-received-msg: la memoria dell'agente sui messaggi passati
(defrule on_meal_req_received
	(declare (salience 14))
	(msg-to-agent (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
	(status (step ?i))
	(test (= ?s ?i))
	(not (K-received-msg (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request meal) (t_pos-r ?tr) (t_pos-c ?tc)))
	(if (eq ?pills before) 
		then
		;Inform di Wait 
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 meal) (param3 wait) (param4 nil)))
		else
		;Inform di Ok 
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 meal) (param3 yes) (param4 nil)))
	)
	;(halt)
)

;(defrule contemporary_informs
;	(declare (salience 14))
;	(status (step ?i))
;	?g <- (proto-exec (step ?s1) (action Inform) (param1 ?P11) (param2 ?P21) (param3 ?P31) (param4 ?P41))	
;	?f <- (proto-exec (step ?s2) (action Inform) (param1 ?P12) (param2 ?P22) (param3 ?P32) (param4 ?P42))
;	(not (K-exec (step ?s2) (action Inform) (param1 ?P12) (param2 ?P22) (param3 ?P32) (param4 ?P42)))
;	(test (and (= ?s1 ?s2) (neq ?f ?g) ))
;	=>
;	(modify ?f (step (+ ?s2 1)))
;)

;Regola che si attiva all'arrivo di una richiesta di dessert.
;Manda subito l'inform, poi strategy si occuperà di come e quando portarla a termine
;Salva inoltre una copia della richiesta in K-received-msg: la memoria dell'agente sui messaggi passati

(defrule on_dessert_req_received_generic
	(declare (salience 14))
	(msg-to-agent (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (pills ?pills) (dessert ?dessert))
	(test (neq ?pills after))
	(status (step ?i))
	(test (= ?s ?i))	
	(not (K-received-msg (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>	
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	(if (eq ?dessert yes) then
		;Accetto la richiesta
		(if (eq ?pills after) then 
			(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 wait) (param4 nil)))
			else
			(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil))) 
		)
		else 
		;Rifiuto della richiesta perché contraria alla prescrizione 
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 reject) (param4 nil)))
	)
)

;specializzazione della regola sovrastante, si attiva solo nei casi di pill after nella prescription
;e se le pillole non sono state ancora consegnate
(defrule on_dessert_req_received_pills_after_dessert_wait
	(declare (salience 14))
	(msg-to-agent (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (pills after) (dessert ?dessert))
	;se non gli sono state consegnate le pillole, deve attendere per il dessert
	(not (K-pill-delivered (person ?P)))
	(status (step ?i))
	(test (= ?s ?i))	
	(not (K-received-msg (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>	
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	(if (eq ?dessert yes) then
		;Accetto la richiesta
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 wait) (param4 nil)))			
		else 
		;Rifiuto della richiesta perché contraria alla prescrizione 
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 reject) (param4 nil)))
	)
)

;specializzazione della regola sovrastante, si attiva solo nei casi di pill after nella prescription
;e se le pillole sono state giù consegnate
(defrule on_dessert_req_received_pills_after_dessert_yes
	(declare (salience 14))
	(msg-to-agent (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc))
	(prescription (patient ?P) (pills after) (dessert ?dessert))
	(K-pill-delivered (person ?P))
	(status (step ?i))
	(test (= ?s ?i))	
	(not (K-received-msg (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	=>	
	;aggiungo il messaggio alla lista dei ricevuti (e già esaminati)
	(assert (K-received-msg (step ?s) (sender ?P) (request dessert) (t_pos-r ?tr) (t_pos-c ?tc)))
	(if (eq ?dessert yes) then
		;Accetto la richiesta
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 yes) (param4 nil))) 
		
		else 
		;Rifiuto della richiesta perché contraria alla prescrizione 
		(assert (proto-exec (step ?s) (action Inform) (param1 ?P) (param2 dessert) (param3 reject) (param4 nil)))
	)
)


; Notifica nella finestra di dialogo che c'è stato un bump, a fini di debugging
(defrule bump_alarm 
	(declare (salience 14))
	(perc-bump (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d) )
	=>
	(printout t crlf crlf)
	(printout t " AGENT" crlf)
	(printout t " WARNING, ho fatto un bump in " ?r " " ?c " andando verso " ?d)         
	(printout t crlf crlf)
	(halt)
)


; Inizio procedura per evitare i bump
(defrule bump_avoid_initiate_repath
	(declare (salience 14))
	(perc-vision (time ?time) (step ?step) (pos-r ?r) (pos-c ?c) (direction ?d) 
		(perc1 ?perc1) (perc2 ?perc2) (perc3 ?perc3) (perc4 ?perc4) (perc6 ?perc6) 
		(perc7 ?perc7) (perc8 ?perc8) (perc9 ?perc9))
	(K-agent (step ?step))
	(proto-exec (todo-id ?id) (step ?step) (action Forward))
	?f <- (K-cell (pos-r ?kr) (pos-c ?kc) (contains ?cont))
	(test  (eq ?perc2 PersonStanding) )
	(test (or (and (eq ?d south) (= ?kr (- ?r 1)) (= ?kc ?c))                
		  (and (eq ?d north) (= ?kr (+ ?r 1)) (= ?kc ?c))                
		  (and (eq ?d east) (= ?kr ?r) (= ?kc (+ ?c 1)))                
		  (and (eq ?d west) (= ?kr ?r) (= ?kc (- ?c 1)))
		)                
	)
	=>
	(printout t crlf crlf)
	(printout t " AGENT" crlf)
	(printout t " bump detected while i am in " ?kr " & " ?kc)         
	(printout t crlf crlf)
	(assert (bump-avoid (todo-id ?id) (step ?step) (pos-r ?kr) (pos-c ?kc) ))
	(modify ?f (contains PersonStanding))
	(focus STRATEGY)
)


(defrule update_agent_penalty
	  (declare (salience 15))
	  ?f <- (K-agent (step ?step) (time ?time) (penalty ?p1))
	  (penalty ?p2)
	  (test (neq ?p1 ?p2))
	  (test (neq ?p2 nil))
	  =>
	  (modify ?f (penalty ?p2))
	  (if (> ?p2 (+ 1000 ?p1))  then 
	  	(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " PENALTY SKY-ROCKETED: something bad happened at step " ?step " an time " ?time crlf)  
		(printout t " penalty increased by " (- ?p2 ?p1) )       
		(printout t crlf crlf)
		(halt)
	)

)

; Fa l'update del fatto K-agent in base alle percezioni visive ricevute e ritira quello dello step precedente
(defrule update_agent_vision 
	(declare (salience 14))
	(perc-vision (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d))
	?f <- (K-agent (step ?sA) (free ?fr) (waste ?w))
	(test (< ?sA ?s))
	=>
	(modify ?f (time ?time) (step ?s) (pos-r ?r) (pos-c ?c) (direction ?d) (free ?fr) (waste ?w))
)	

; Fa l'update del fatto K-agent in base alle percezioni di carico ricevute e ritira quello dello step precedente
; Si attiva dopo che è stata eseguita una LoadMeal
(defrule update_agent_load_meal
	(declare (salience 15))
	?e <- (perc-load (step ?step) (load yes))
	?f <- (K-agent (free ?fr) (content $?cont))	
	(K-exec (step ?step2) (action LoadMeal) (param1 ?posr) (param2 ?posc) (param3 ?type))
	
	(test (= ?step (+ ?step2 1)))	
	=>
	(if (> ?fr 0)
		then
		( if (eq ?fr 2) 
			then  	
				(modify ?f (step ?step) (free (- ?fr 1)) (content ?type) )
			else  (modify ?f (step ?step) (free (- ?fr 1)) (content (insert$ $?cont 1 ?type)) )
			)
		
		else        
		(printout t crlf crlf)
		(printout t "AGENT")
		(printout t "errore, Agente pieno")         
		(printout t crlf crlf)
		(halt)
	)	
	(retract ?e)	
)

; Fa l'update del fatto K-agent in base alle percezioni di carico ricevute e ritira quello dello step precedente
; Si attiva dopo l'esecuzione di LoadDessert
(defrule update_agent_load_dessert
	(declare (salience 15))
	?e <- (perc-load (step ?step) (load yes))
	?f <- (K-agent (free ?fr) (content $?cont))	
	(K-exec (step ?step2) (action LoadDessert) (param1 ?posr) (param2 ?posc))
	
	(test (= ?step (+ ?step2 1)))	
	=>
	(if (> ?fr 0)
		then
		(modify ?f (step ?step) (free (- ?fr 1)) (content (insert$ $?cont 1 dessert)) )
		; (printout t crlf crlf)
		; (printout t " AGENT" crlf)
		; (printout t " __________________" crlf)
		; (printout t " CARICATO UN DESSERT ")     

		; (printout t " __________________" crlf)    
		; (printout t crlf crlf)
		
		else        
		(printout t crlf crlf)
		(printout t "AGENT")
		(printout t "errore, Agente pieno")         
		(printout t crlf crlf)
		(halt)
	)	
	(retract ?e)	
)

; Fa l'update del fatto K-agent in base alle percezioni di carico ricevute e ritira quello dello step precedente
; Si attiva dopo che è stata eseguita una LoadMeal
(defrule update_agent_load_pill
	(declare (salience 15))
	?e <- (perc-load (step ?step) (load yes))
	?f <- (K-agent (free ?fr) (content $?cont))	
	(K-exec (step ?step2) (action LoadPill) (param1 ?posr) (param2 ?posc) (param3 ?P))	
	(test (= ?step (+ ?step2 1)))	
	=>
	(if (> ?fr 0)
		then
		( if (eq ?fr 2) 
			then  	
				(modify ?f (step ?step) (free (- ?fr 1)) (content ?P) )
			else  (modify ?f (step ?step) (free (- ?fr 1)) (content (insert$ $?cont 1 ?P)) )
			)
		
		else        
		(printout t crlf crlf)
		(printout t "AGENT" crlf)
		(printout t "errore, Agente pieno")         
		(printout t crlf crlf)
		;(halt)
	)	
	(retract ?e)	
)

(defrule update_agent_load_trash
	(declare (salience 15))
	;(perc-load (step ?step) (load yes))
    	?f <- (K-agent (step ?step) )
    	?g <- (K-table (t_pos-r ?tr) (t_pos-c ?tc) (clean no))
    	(K-exec (step ?step2) (action CleanTable) (param1 ?tr) (param2 ?tc) (param3 ?p3) (param4 ?p4))
    	(test (= ?step (+ ?step2 1)))	
    	=>
    	(modify ?f (step ?step) (waste yes) ) 
    	(modify ?g (clean yes))
    	(printout t crlf crlf)
	(printout t " AGENT" crlf)
	(printout t " Caricata spazzatura")         
	(printout t crlf crlf)    	
	
)

; Sceglie l'elemento da scaricare nella lista
; La regola agisce su pill e meals
(defrule update_agent_unload_pill_or_meal
	(declare (salience 15))		
	;?e <- (perc-load (step ?step) (load no))
	(K-exec (step ?step1) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3))
	?f <- (K-agent (step ?step1) (content $?c) (free ?fr))
	?g <- (K-received-msg (request ?req) (t_pos-r ?p1) (t_pos-c ?p2) (taken yes))		
	(test (< ?fr 2))
	;(test (= ?step (+ ?step1 1)))
	(test (member$ ?p3 $?c))
	(test (or (eq ?a DeliveryMeal) (eq ?a DeliveryPill)))
	=> 
	(modify ?f (step (+ ?step1 1)) (content (delete-member$ $?c ?p3)) (free (+ ?fr 1)))
	(if  (eq ?a DeliveryPill) 
		then (assert (K-pill-delivered (person ?p3)))
	)		
	(modify ?g (completed yes))	
)

; Sceglie l'elemento da scaricare nella lista
; La regola agisce su desserts
(defrule update_agent_unload_dessert
	(declare (salience 15))		
	;?e <- (perc-load (step ?step) (load no))
	(K-exec (step ?step1) (action DeliveryDessert) (param1 ?p1) (param2 ?p2))
	?f <- (K-agent (step ?step1) (content $?c) (free ?fr))
	?g <- (K-received-msg (request ?req) (t_pos-r ?p1) (t_pos-c ?p2) (taken yes))		
	(test (< ?fr 2))
	;(test (= ?step (+ ?step1 1)))
	(test (member$ dessert $?c))	
	=> 
	(modify ?f (step (+ ?step1 1)) (content (delete-member$ $?c dessert)) (free (+ ?fr 1)))		
	(modify ?g (completed yes))
; 	(printout t "DESSERT UNLOADED")
; 	(halt)	
)


(defrule update_agent_unload_trash
	(declare (salience 15))	
	(K-exec (step ?step1) (action ReleaseTrash) (param1 ?p1) (param2 ?p2) (param3 ?p3))
	?f <- (K-agent (step ?step2) (waste yes))
	(test (= (- ?step2 1) ?step1))	
	;(test (= ?step (+ ?step1 1)))
	=> 
	(modify ?f (waste no) )
)

;Trasforma una proto-exec in una exec
;a meno che non ci siano già delle exec stabilite per questo turno, come delle inform
(defrule assert_exec	
	(declare (salience 12))
	(K-agent (step ?step))
	?f <- (proto-exec (todo-id ?id) (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4) (last-action ?value))
	(not (exec (step ?step) ))
	=>
	(assert (exec (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4)))
	(if (eq ?value yes) 
		then (assert (executed-todo (todo-id ?id)))
	)
	(retract ?f)
)

;Manda in exec un'exec già presente - come nel caso delle inform
;aggiora eventuali azioni proto-exec programmate aumentando il contatore di step
(defrule assert_exec_proto-exec_conflict	
	(declare (salience 12))
	(K-agent (step ?step))
	(exec (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4))
	?f <- (proto-exec (todo-id ?id) (step ?step) )
	;?g <- (proto-exec (todo-id ?id) (step ?step1) )
	;(test (> ?step1 ?step))	
	=>
	(assert (proto-exec-reorder))
	;(modify ?f (step (+ ?step 1)))
	;(modify ?g (step (+ ?step1 1)))	
)

;Manda in exec un'exec già presente - come nel caso delle inform
;aggiora eventuali azioni proto-exec programmate aumentando il contatore di step
;(defrule assert_proto-exec_conflict	
;	(declare (salience 12))
;	(K-agent (step ?step))
;	(proto-exec (todo-id ?id1) (step ?step) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4))
;	?f <- (proto-exec (todo-id ?id2) (step ?step) )
	;?g <- (proto-exec (todo-id ?id) (step ?step1) )
;	(test (neq ?id1 ?id2))	
;	=>
;	(assert (proto-exec-reorder))
	;(modify ?f (step (+ ?step 1)))
	;(modify ?g (step (+ ?step1 1)))	
;)

(defrule proto-exec_order_fix_init	
	(declare (salience 12))
	?h <- (proto-exec-reorder (reorder-step nil))
	?f <- (proto-exec (todo-id ?id) (step ?step) )
	(not (proto-exec (todo-id ?id) (step ?step1&:(> ?step1 ?step))))
	;(test (> ?step1 ?step))	
	=>
	(modify ?h (reorder-step ?step))
	;(modify ?g (step (+ ?step1 1)))	
)

(defrule proto-exec_order_fix	
	(declare (salience 12))
	(K-agent (step ?step))
	?h <- (proto-exec-reorder (reorder-step ?rs))
	(test (and (neq ?rs nil) (neq ?rs (- ?step 1) ) ))
	?f <- (proto-exec (todo-id ?id) (step ?rs) )	
	;(test (> ?step1 ?step))	
	=>	
	(modify ?f (step (+ ?rs 1)))
	(modify ?h (reorder-step (- ?rs 1)))
)

(defrule proto-exec_order_clean
	(declare (salience 12))
	(K-agent (step ?step))
	?h <- (proto-exec-reorder (reorder-step ?rs))
	(test (eq ?rs (- ?step 1) ) )
	=>
	(retract ?h)
)

(defrule update_table_dirty
	(declare (salience 3))
	(status (step ?i) (time ?t))
    	(K-agent (step ?i) (pos-r ?r) (pos-c ?c) (direction ?dir))
    	(exec (step ?j) (action DeliveryMeal) (param1 ?tr) (param2 ?tc) (param3 ?p3) (param4 ?p4))
    	(test (= (+ ?j 1) ?i))
    	
    	?f <- (K-table (t_pos-r ?tr) (t_pos-c ?tc) (clean yes))
    	=>
    	(modify ?f (clean no) (meal_delivered_at_time ?t) )
)


;Controlla se ci sono delle exec programmate per questo step e le manda in esecuzione		
(defrule exec_act
	(declare (salience 2))
    	(K-agent (step ?i) (time ?time) (pos-r ?r) (pos-c ?c) (direction ?dir))
    	(exec (step ?i) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4))    	
   	=> 
     	(assert (K-exec (step ?i) (action ?a) (param1 ?p1) (param2 ?p2) (param3 ?p3) (param4 ?p4)))

     	;Stampe a console
     	(if (or (eq ?a DeliveryMeal) (eq ?a DeliveryPill) (eq ?a DeliveryDessert)) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		;(printout t " __________________" crlf)
		(printout t " Delivery Action " ?a  " at step " ?i " while I am in " ?r " & " ?c " in time " ?time crlf)
		;(halt)
		(printout t " Params " ?p1 " " ?p2 " " ?p3 " " ?p4 )         
		(printout t crlf crlf)
		;(if (eq ?a DeliveryDessert) then (halt) )

	)

	(if (or (eq ?a LoadMeal) (eq ?a LoadDessert) (eq ?a LoadPill)) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Load Action " ?a  " at step " ?i " while I am in " ?r " & " ?c " in time " ?time crlf)
		(printout t " Params " ?p1 " " ?p2 " " ?p3 " " ?p4 )           
		(printout t crlf crlf)
	)

	; (if (eq ?a Forward) 
 ;     		then
	; 	(printout t crlf crlf)
	; 	(printout t " AGENT" crlf)
	; 	(printout t " going forward from " ?r " & " ?c " facing " ?dir)         
	; 	(printout t crlf crlf)
	; )

	; (if (eq ?a EmptyRobot) 
 ;     		then
	; 	(printout t crlf crlf)
	; 	(printout t " AGENT" crlf)
	; 	(printout t " Emptied Robot Trash in " ?r " & " ?c " facing " ?dir)         
	; 	(printout t crlf crlf)
	; )

	(if (eq ?a CleanTable) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Cleaned table near " ?r " & " ?c " facing " ?dir " in time " ?time) 
		;(halt)        
		(printout t crlf crlf)
		
	)
	(if (eq ?a Inform) 
     		then
		(printout t crlf crlf)
		(printout t " AGENT" crlf)
		(printout t " Informing " ?p1 " of request " ?p2 " result " ?p3)         
		(printout t crlf crlf)		
	)
	; (if (eq ?a Wait) 
 ;     		then
	; 	(printout t crlf crlf)
	; 	(printout t " WAIT" crlf)
    
	; 	(printout t crlf crlf)		
	; )
       	(focus MAIN)
)


;Se è stato ricevuto un messaggio, passa il controllo a Strategy per far si
;che lo traduca in un todo
;NOTA : la salience è più bassa di exec_act, probabilmente questa regola si attiva se non ci sono exec da fare.
;NON è detto che vada bene.
(defrule message_received_this_step
	(declare (salience 1))
	(K-received-msg (step ?step) )
	(K-agent (step ?step))
	=>
	(focus STRATEGY)
)


; Comunica DONE quando il tempo sta per scadere
(defrule DONE_act
	(declare (salience 1))
 	?f <-   (status (step ?i) (time ?t))
 	(K-agent (pos-r ?r) (pos-c ?c))
 	(max_duration (time ?maxt))
 	(not (status (step 0)))
 	(test (> ?t (- ?maxt 31)))
    	=>  
    	(printout t crlf crlf)
	(printout t " AGENT" crlf)
	(printout t " Sending DONE message while in " ?r " & " ?c )         
	(printout t crlf crlf)	
        (modify ?f (work on))
        (assert (exec (step ?i) (action Done)))			
)

(defrule nothing_else_todo
 	(declare (salience 0))      
      	=>  
     	(focus STRATEGY)	
)

; 
