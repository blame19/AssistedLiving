;// STRATEGY FIFO

(defmodule STRATEGY (import MAIN ?ALL)   (export ?ALL) (import AGENT ?ALL))



;//_______Facts

;struttura di un path. Non viene riempito da STRATEGY, ma da path; è qu solo perché in questo modo sono entrambi visibili
(deftemplate path  (slot id) (slot obj-id)
        (slot from-r) (slot from-c) 
        (slot start-dir) 
        (slot to-r) (slot to-c) 
        (slot cost) (slot solution (allowed-values yes no) (default no))
)

;fatti della lista delle azioni da fare
(deftemplate todo 
        (slot id)
        (slot priority (default 10))
        (slot cost)
        (slot chosen_path)
        ;utility
        (slot completed (default no))
        (slot expanded (default no))        
        (slot informed (default no))
        ;slot per contenere i dati dai messaggi dell'agente
        (slot request)
        (slot request-time) 
        (slot step)
        (slot sender)          
        (slot goal_pos-r) 
        (slot goal_pos-c)
        )

;per chiedere a PATH di calcolare un percorso
(deftemplate path-request
        (slot id) (slot from-r) (slot from-c) (slot to-r) (slot to-c) (slot start-dir) (slot solution))

;per chiedere a ACTION di tradurre un todo in una lista di EXEC
(deftemplate exec-todo (slot id))

(deftemplate path-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))

(deftemplate todo-counter (slot id))

(deftemplate action-notify (slot bump))
(deftemplate now-serving (slot time) (slot person))

;//_______Rules

(defrule initialize_todo_count 
        (declare (salience 15))
        (not (todo-counter (id ?id)))
        =>
        (assert (todo-counter (id 0)))
)

(defrule completed_todo
        (declare (salience 15))
        ?g <- (executed-todo (todo-id ?id) )
        ?f <- (todo (id ?id) (request ?req))
        =>
        (modify ?f (completed yes))
        (printout t crlf crlf)
        (printout t " STRATEGY" crlf)
        (printout t " Completed todo " ?req)    
        (printout t crlf crlf)
        (retract ?g)
)

;distrugge il vecchio piano
(defrule bump_remove_proto_exec
        (declare (salience 16))        
        (bump-avoid (todo-id ?todo-id) (step ?step) (pos-r ?kr) (pos-c ?kc))
        ?f <- (proto-exec)   
        =>
        (assert (action-notify (bump yes)))
        (retract ?f)
)

(defrule bump_change_todo_path
        (declare (salience 15))
        (K-agent (direction ?sdir) (pos-r ?r) (pos-c ?c))
        ?f <- (bump-avoid (todo-id ?todo-id) (step ?step) (pos-r ?kr) (pos-c ?kc))
        ?g <- (todo (id ?todo-id) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (request-time ?req-time) (step ?step2) (sender ?sender))
        ?i <- (todo-counter (id ?id))
        =>
        ;viene asserito un nuovo todo con nuovo id, e un nuovo fatto di tipo exec-todo con il suo id.
        ;in questo modo si esclude il todo precedente (che viene cancellato) e si forza PATH a ricalcolare il percorso
        (assert (todo (priority 6) (id ?id) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (request-time ?req-time) (step ?step2) (sender ?sender)))
        (assert (path-request (id ?id) (from-r ?r) (from-c ?c) (to-r ?gr) (to-c ?gc) (start-dir ?sdir) (solution nil)))
        ;(modify ?h (id ?id))
        (assert (exec-todo (id ?id)))
        (modify ?i (id (+ ?id 1)))
        (retract ?g)
        (retract ?f)
        (focus PATH)
)

;nella nuova implementazione, questo dovrebbe raccogliere i messaggi dall'agente e 
;fornire una lista di "azioni da fare" da ordinare poi in un piano
(defrule todo_from_message_to_agent      
        (declare (salience 10))        
        ?g <- (msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        ?f <- (K-received-msg (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))        
        (K-agent (step ?step) (content $?con) (free ?free) (waste ?waste))   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dess))
        (K-cell (pos-r ?mdisp-r) (pos-c ?mdisp-c) (contains MealDispenser))
        (K-cell (pos-r ?pdisp-r) (pos-c ?pdisp-c) (contains PillDispenser))        
        (K-cell (pos-r ?ddisp-r) (pos-c ?ddisp-c) (contains DessertDispenser))
        ?h <- (todo-counter (id ?id))
        =>
        (if (eq ?request meal)
                then 
                (switch ?pills 
                    (case no then 
                        (assert (todo (priority 10) (id ?id) (step ?s) (sender ?P) (request meal) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                        (modify ?h (id (+ ?id 1))) 
                    )
                    (case before then 
                        (assert (todo (priority 10) (id ?id)  (step ?s) (sender ?P) (request meal_before) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                        (modify ?h (id (+ ?id 1)))   
                    )
                    (case after then   
                        (assert (todo (priority 10) (id ?id) (step ?s) (sender ?P) (request meal_after) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                        (modify ?h (id (+ ?id 1)))
                    )                        
                )
        )         
        (if (and (eq ?request dessert) (eq ?dess yes))
                then
                (assert (todo (priority 10) (id ?id) (step ?s) (sender ?P) (request dessert) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                (modify ?h (id (+ ?id 1)))
        )

        ;una volta preso carico della richiesta con un todo, cancella il messaggio
        ;ATTENZIONE! bisogna essere certi di aver trattato la richiesta in qualche modo, ovvero
        ;che il TODO sia stato generato
        (retract ?g)
)

;gestisce i todo di meal senza pillole annesse
(defrule todo_simple_meal_expand  
        (declare (salience 10))        
        ?f <- (todo (expanded no) (request-time ?rqt) (completed no) (step ?s) (sender ?P) (request meal))
        (K-cell (pos-r ?mdisp-r) (pos-c ?mdisp-c) (contains MealDispenser))
        (K-agent (step ?step) (content $?con) (free ?free) )   
        (prescription (patient ?P) (meal ?meal))
        ?h <- (todo-counter (id ?id))
        ;(test (or (> ?free 0) (and (eq ?free 0) (member$ ?meal $?con)) ) )
        (test (> ?free 0))
        =>
        ;GET THE MEAL
        (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
        (modify ?h (id (+ ?id 1)))
        (modify ?f (expanded yes))
)

;gestisce i todo di meal_before
(defrule todo_meal_before_expand  
        (declare (salience 10))        
        ?f <- (todo (expanded no) (request-time ?rqt) (completed no) (step ?s) (sender ?P) (request meal_before))
        (K-cell (pos-r ?mdisp-r) (pos-c ?mdisp-c) (contains MealDispenser))
        (K-cell (pos-r ?pdisp-r) (pos-c ?pdisp-c) (contains PillDispenser))   
        (K-cell (pos-r ?trash-r) (pos-c ?trash-c) (contains TrashBasket))
        (K-agent (step ?step) (content $?con) (free ?free) )   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
        ?h <- (todo-counter (id ?id))
         (test (or (eq ?free 2) (and (eq ?free 1) (or (member$ ?P $?con) (member$ ?meal $?con)) ) ))
        =>        
        (if (eq ?free 2)
                then 
                ;GET THE MEAL AND PILLS
                (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
                (assert (todo (id (+ ?id 1)) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_pills) (goal_pos-r ?pdisp-r) (goal_pos-c ?pdisp-c)) )      
                (modify ?h (id (+ ?id 2)))
                (modify ?f (expanded yes))

       
                else
                (if (or (and (eq ?free 1) (member$ ?P $?con) )
                        (and (eq ?free 1) (member$ ?meal $?con) )
                        )
                        then ;MEAL OR PILLS ALREADY ON - GET THE OTHER
                        (if (member$ ?P $?con) 
                                then ;PILLS OK GET MEAL
                                (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
                                (modify ?h (id (+ ?id 1)))
                                (modify ?f (expanded yes))
                        )
                        (if (member$ ?meal $?con) 
                                then ;MEAL OK GET PILLS
                                (assert (todo (id (+ ?id 1)) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_pills) (goal_pos-r ?pdisp-r) (goal_pos-c ?pdisp-c)) )      
                                (modify ?h (id (+ ?id 1)))
                                (modify ?f (expanded yes))
                        )
                        else ;NO SPACE FOR MEAL AND PILLS
                        ;MAKE SPACE FOR MEAL AND PILLS
                        (printout t crlf crlf)
                        (printout t " STRATEGY" crlf)
                        (printout t " WARNING: l'agente non ha spazio per caricare pranzo e pillole insieme" )
                        (printout t crlf crlf)
                        ;generazione dei todo per svuotare il load dell'agente e caricare un nuovo pranzo 
                        ;(modify ?f (expanded yes))

                )
        )
)

;gestisce i todo di meal_after
;NOTA: al momento uguale a meal_before ... cambia solo in action
(defrule todo_meal_after_expand  
      (declare (salience 10))        
        ?f <- (todo (expanded no) (request-time ?rqt) (completed no) (step ?s) (sender ?P) (request meal_after))
        (K-cell (pos-r ?mdisp-r) (pos-c ?mdisp-c) (contains MealDispenser))
        (K-cell (pos-r ?pdisp-r) (pos-c ?pdisp-c) (contains PillDispenser))   
        (K-cell (pos-r ?trash-r) (pos-c ?trash-c) (contains TrashBasket))
        (K-agent (step ?step) (content $?con) (free ?free) )   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
        ?h <- (todo-counter (id ?id))
        (test (or (eq ?free 2) (and (eq ?free 1) (or (member$ ?P $?con) (member$ ?meal $?con)) ) ))
        =>
        (if (eq ?free 2)
                then 
                ;GET THE MEAL AND PILLS
                (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
                (assert (todo (id (+ ?id 1)) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_pills) (goal_pos-r ?pdisp-r) (goal_pos-c ?pdisp-c)) )      
                (modify ?h (id (+ ?id 2)))
                (modify ?f (expanded yes))
                else
                (if (or (and (eq ?free 1) (member$ ?P $?con) )
                        (and (eq ?free 1) (member$ ?meal $?con) )
                        )
                        then ;MEAL OR PILLS ALREADY ON - GET THE OTHER
                        (if (member$ ?P $?con) 
                                then ;PILLS OK GET MEAL
                                (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
                                (modify ?h (id (+ ?id 1)))
                                (modify ?f (expanded yes))
                        )
                        (if (member$ ?meal $?con) 
                                then ;MEAL OK GET PILLS
                                (assert (todo (id (+ ?id 1)) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_pills) (goal_pos-r ?pdisp-r) (goal_pos-c ?pdisp-c)) )      
                                (modify ?h (id (+ ?id 1)))
                                (modify ?f (expanded yes))
                        )
                        else ;NO SPACE FOR MEAL AND PILLS
                        ;MAKE SPACE FOR MEAL AND PILLS
                        (printout t crlf crlf)
                        (printout t " STRATEGY" crlf)
                        (printout t " WARNING: l'agente non ha spazio per caricare pranzo e pillole insieme" )
                        (printout t crlf crlf)
                        ;generazione dei todo per svuotare il load dell'agente e caricare un nuovo pranzo 
                        ;(modify ?f (expanded yes))

                )
        )
)

(defrule todo_dessert_expand  
        (declare (salience 10))        
        ?f <- (todo (expanded no) (request-time ?rqt) (completed no) (step ?s) (sender ?P) (request dessert))         
        (K-cell (pos-r ?ddisp-r) (pos-c ?ddisp-c) (contains DessertDispenser))
        (K-cell (pos-r ?trash-r) (pos-c ?trash-c) (contains TrashBasket))
        (K-agent (step ?step) (content $?con) (free ?free) )   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert yes))
        ?h <- (todo-counter (id ?id))
        (K-agent (step ?step))
        =>
        ;se la persona ha diritto a quel dessert
        (if (eq free 0)
            then 
            ;MAKE SPACE
            (printout t crlf crlf)
            (printout t " STRATEGY" crlf)
            (printout t " WARNING: l'agente non ha spazio per caricare il dessert" )
            (printout t crlf crlf)
            else
            ;GET THE DESSERT
            (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_dessert) (goal_pos-r ?ddisp-r) (goal_pos-c ?ddisp-c)) )
            (modify ?h (id (+ ?id 1)))
            (modify ?f (expanded yes))
        )  
)



(defrule todo_clean_table_dessert_requested
        (declare (salience 11))   
        (K-agent (step ?step) (time ?time))
        (K-table (t_pos-r ?tr) (t_pos-c ?tc) (clean no) (meal_delivered_at_time ?mdt))
        (test (neq ?mdt nil))
        (K-received-msg (t_pos-r ?tr) (t_pos-c ?tc) (sender ?P) (request dessert)) 
        (not (todo (request clean_table) (completed no) (goal_pos-r ?tr) (goal_pos-c ?tc)))
        ?h <- (todo-counter (id ?id))
        =>
        (assert (todo (id ?id) (priority 11) (request-time ?time) (step ?step) (sender nil) (request clean_table) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
        (modify ?h (id (+ ?id 1)))
   
                                 
)

(defrule todo_clean_table_meal_duration
        (declare (salience 11))   
        (K-agent (step ?step) (time ?time))
        (max_duration (time ?maxt))
        (K-table (t_pos-r ?tr) (t_pos-c ?tc) (clean no) (meal_delivered_at_time ?time2))
        ;(test (or (< (- ?maxt ?time) 50)  (> ?time (+ 500 ?time2)) ))
        (test (and (> ?time (+ 501 ?time2)) (neq ?time2 nil)) )
        (not (todo (request clean_table) (completed no) (goal_pos-r ?tr) (goal_pos-c ?tc)))
        ?h <- (todo-counter (id ?id))
        =>
        (assert (todo (id ?id) (priority 11) (request-time ?time) (step ?step) (sender nil) (request clean_table) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
        (modify ?h (id (+ ?id 1)))                                 
)

;gestisce i todo di meal senza pillole annesse
(defrule todo_empty_trash
        (declare (salience 11))        
        (K-cell (pos-r ?trash-r) (pos-c ?trash-c) (contains TrashBasket))
        (K-agent (step ?step) (waste yes) (time ?time))
        (not (todo (request empty_trash) (completed no) (goal_pos-r ?tr) (goal_pos-c ?tc)))   
        ?h <- (todo-counter (id ?id))        
        =>
        (assert (todo (id ?id) (priority 7) (request-time ?time) (step ?step) (sender nil) (request empty_trash) (goal_pos-r ?trash-r) (goal_pos-c ?trash-c)) )
        (modify ?h (id (+ ?id 1)))    
)

;Stima il costo delle azioni basandosi su un'euristica manhattan del percorso più il costo temporale della singola azione specifica
(defrule todo_cost_estimate_manhattan_action
        (declare (salience 10))
        ?f <- (todo (id ?todo-id) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (cost nil))
        (K-agent (pos-r ?r) (pos-c ?c))
        =>
        (switch ?req 
                (case load_dessert then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 10)) ))
                (case load_pills then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 10)) ))
                (case load_meal then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 15)) ))
                (case meal then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 12)) ))
                (case meal_before then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 22)) ))
                (case meal_after then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 22)) ))
                (case dessert then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 10)) ))
                (case clean_table then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 30)) ))
                (case empty_trash then  (modify ?f (cost (+ (manhattan ?r ?c ?gr ?gc) 10)) ))
        )
       
)

;Scelta del todo da eseguire. 
;Strategia FIFO con priorità.
;Questa regola si attiva se l'agente è libero e se non sta servendo nessuno.  
(defrule strategy_choose_FIFO_agent_free
        (declare (salience 8))
        (not (now-serving))
        ?f <- (todo (id ?todo-id) (chosen_path ?path-id) (cost ?c1) (priority ?priority) (step ?s) (sender ?P) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (completed no))
        (not (todo (completed no) (step ?s2&:(<= ?s2 ?s)) (priority ?pr2&:(< ?pr2 ?priority))  ))
        (not (exec-todo ))
        (K-agent (pos-r ?r) (pos-c ?c) (direction ?sdir) (waste ?waste) (free ?free))
        (test (not (and (eq ?waste yes) (or (eq ?req load_meal) (eq ?req load_dessert) (eq ?req load_pills)  (eq ?req dessert) (eq ?req meal) (eq ?req meal_before) (eq ?req meal_after) ))) )
        (test (not (and (< ?free 2) (eq ?req clean_table) )))
        (test (> ?free 0))
        => 
        (printout t crlf crlf)
        (printout t " STRATEGY" crlf)     
        (printout t " execute todo " ?todo-id " requiring action " ?req " at " ?gr " & " ?gc)
        (printout t crlf crlf)
        (assert (path-request (id ?todo-id) (from-r ?r) (from-c ?c) (to-r ?gr) (to-c ?gc) (start-dir ?sdir) (solution nil)))
        (if (neq ?P nil) then (assert (now-serving (person ?P))))
        (focus PATH)
        (assert (exec-todo (id ?todo-id))) 
)

;Scelta del todo da eseguire. 
;Strategia FIFO con priorità.
;Questa regola si attiva se l'agente non è libero e se non sta servendo nessuno.  
(defrule strategy_choose_FIFO_agent_not_free
        (declare (salience 8))
        (not (now-serving))        
        ?f <- (todo (id ?todo-id) (chosen_path ?path-id) (cost ?c1) (priority ?priority) (step ?s) (sender ?P) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (completed no))
        (not (exec-todo))
        (K-agent (pos-r ?r) (pos-c ?c) (direction ?sdir) (waste ?waste) (free 0))
        (test (and (neq ?req load_meal) (neq ?req load_dessert) (neq ?req load_pills)  (neq ?req clean_table) ))
        => 
        (printout t crlf crlf)
        (printout t " STRATEGY" crlf)     
        (printout t " execute todo " ?todo-id " requiring action " ?req " at " ?gr " & " ?gc)
        (printout t crlf crlf)
        (assert (path-request (id ?todo-id) (from-r ?r) (from-c ?c) (to-r ?gr) (to-c ?gc) (start-dir ?sdir) (solution nil)))
        (focus PATH)
        (assert (exec-todo (id ?todo-id))) 
)

;Scelta del todo da eseguire. 
;Strategia FIFO con priorità.
;Questa regola si attiva se l'agente è libero e se ha iniziato già a servire qualcuno.  
(defrule strategy_choose_person_agent_free
        (declare (salience 8))
        (now-serving (person ?P))
        ?f <- (todo (id ?todo-id) (chosen_path ?path-id) (cost ?c1) (priority ?priority) (step ?s) (sender ?P) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (completed no))
        (not (todo (completed no)  (sender ?P) (step ?s2&:(<= ?s2 ?s)) (priority ?pr2&:(< ?pr2 ?priority))  ))
        (not (exec-todo)) 
        (K-agent (pos-r ?r) (pos-c ?c) (direction ?sdir) (waste ?waste) (free ?free))
        (test (not (and (eq ?waste yes) (or (eq ?req load_meal) (eq ?req load_dessert) (eq ?req load_pills)  (eq ?req dessert) (eq ?req meal) (eq ?req meal_before) (eq ?req meal_after) ))) )
        (test (not (and (< ?free 2) (eq ?req clean_table) )))
        (test (> ?free 0))
        => 
        (printout t crlf crlf)
        (printout t " STRATEGY" crlf)     
        (printout t " execute todo " ?todo-id " requiring action " ?req " at " ?gr " & " ?gc)
        (printout t crlf crlf)
        (assert (path-request (id ?todo-id) (from-r ?r) (from-c ?c) (to-r ?gr) (to-c ?gc) (start-dir ?sdir) (solution nil)))
        (if (neq ?P nil) then 
                (assert (now-serving (person ?P)))
 ;               (printout t crlf crlf)
 ;               (printout t " STRATEGY" crlf)     
 ;               (printout t " Asserting now-serving fact for " ?P)
 ;               (printout t crlf crlf)
                )
        (focus PATH)
        (assert (exec-todo (id ?todo-id))) 
)

;Scelta del todo da eseguire. 
;Strategia FIFO con priorità.
;Questa regola si attiva se l'agente non è libero e se ha iniziato già a servire qualcuno. 
(defrule strategy_choose_person_agent_not_free
        (declare (salience 8))
        (now-serving (person ?P))  
        ?f <- (todo (id ?todo-id) (chosen_path ?path-id) (cost ?c1) (priority ?priority) (step ?s) (sender ?P) (request ?req) (goal_pos-r ?gr) (goal_pos-c ?gc) (completed no))
        (not (exec-todo ))
        (K-agent (pos-r ?r) (pos-c ?c) (direction ?sdir) (waste ?waste) (free 0))
        (test (and (neq ?req load_meal) (neq ?req load_dessert) (neq ?req load_pills)  (neq ?req clean_table) ))
        => 
        (printout t crlf crlf)
        (printout t " STRATEGY" crlf)     
        (printout t " execute todo " ?todo-id " requiring action " ?req " at " ?gr " & " ?gc)
        (printout t crlf crlf)
        (assert (path-request (id ?todo-id) (from-r ?r) (from-c ?c) (to-r ?gr) (to-c ?gc) (start-dir ?sdir) (solution nil)))
        (focus PATH)
        (assert (exec-todo (id ?todo-id))) 
)

;ritrae i fatti di tipo now serving.
(defrule finished_serving
        (declare (salience 9))
        ?f <- (now-serving (person ?P))
        (not  (todo (sender ?P) (completed no) ))
        =>
;         (printout t crlf crlf)
;        (printout t " STRATEGY" crlf)     
;        (printout t " retracting now-serving fact for " ?P)
;        (printout t crlf crlf)
        (retract ?f)
)


;Sceglie il miglior path tra quelli proposti dal modulo PATH.
(defrule choose_best_path
        (declare (salience 10))
        ?f <- (todo (id ?todo-id) (request ?req) (chosen_path nil))        
        (path (id ?path-id) (obj-id ?todo-id) (cost ?cost1) (solution yes) (to-r ?tr) (to-c ?tc))
        (not (path (obj-id ?todo-id) (cost ?cost2&:(< ?cost2 ?cost1)) (solution yes)))
        ; (K-agent (pos-r ?r) (pos-c ?c) (direction ?sdir))
        ; ?g <- (path-request (id ?id) (from-r ?r) (from-c ?c) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
        =>
        (modify ?f (cost ?cost1) (chosen_path ?path-id))
        ; (retract ?g)
)

(defrule pass_to_action
        (declare (salience 8))
        (exec-todo (id ?todo-id))
        (todo (id ?todo-id) (chosen_path ?path-id))
        =>
        (if (neq ?path-id nil)
                then
                (focus ACTION)
                else
                (printout t crlf crlf)
                (printout t " STRATEGY" crlf)
                (printout t " errore: ho selezionato un todo senza path associato" )
                (printout t crlf crlf)
        )
)

(defrule no_todo_then_wait
        (declare (salience 0))
        (K-agent (step ?i))       
        =>
         (assert (exec (step ?i) (action Wait)))        
                (focus AGENT)
)


; (defrule test_HALT_debug
;         (declare (salience 100))
;         ;(todo (sender ?P))
;         (now-serving (person P6))
;         =>
;         (halt)
;         )