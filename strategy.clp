;// STRATEGY

(defmodule STRATEGY (import MAIN ?ALL)   (export ?ALL) (import AGENT ?ALL))



;//_______Facts

;Fatto aggregato da passare ad Action 
; che contiene tutte le informazioni necessarie per soddisfare la richiesta, generando un piano
;ricordarsi che se necessario gli slot possono essere lasciati a null
;(deftemplate to-action
;       (slot step)
;        (slot sender)
;        ;request, per esempio meal e dessert (dall'ENV) o nostre personalizzate (trash, pills, goback, clean_table eccetera)
        ; eventualmente anche staccate (take_meal, take_dessert)
;        (slot request)
        ;se la richista prevede la posizione (normale, di cella vuota)
;        (slot pos-r) (slot pos-c)
        ;se la richiesta prevede la posizione di un tavolo o di un dispenser
;        (slot t_pos-r) (slot t_pos-c)
        ;parametri opzionali
;        (slot type_of_meal)
;        (slot pills)
;        (slot completed (allowed-values yes no))
;)

;struttura di un path. Non viene riempito da STRATEGY, ma da path; è qu solo perché in questo modo sono entrambi visibili
(deftemplate path  (slot id) (slot obj-id)
        (slot from-r) (slot from-c) 
        (slot start-dir) 
        (slot to-r) (slot to-c) 
        (slot cost) (slot solution (allowed-values yes no) (default no))
)

;fatti della lista delle azioni da fare
(deftemplate todo 
        ;slot per la nozione di priorità (TODO: come scegliere tra varie azioni da fare?)
        (slot id)
        (slot priority (default 10))
        (slot cost)
        (slot chosen_path)
        ;utility
        (slot expanded (default no))
        ;slot per contenere i dati dai messaggi dell'agente
        (slot request-time) 
        (slot step)
        (slot sender) 
        (slot request) 
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

;//_______Rules

; (defrule TESTNEWPATH
;         (declare (salience 16))
;         (not (status (step 0)))
;         =>
;         (assert (path-request (id 0) (from-r 8) (from-c 6) (to-r 4) (to-c 4) (start-dir north) ))
;         )

(defrule initialize_todo_count 
        (declare (salience 15))
        (not (todo-counter (id ?id)))
        =>
        (assert (todo-counter (id 0)))
)


(defrule ask_path
        (declare (salience 10))
        (path-request (id ?id) (from-r ?r) (from-c ?c) (to-r ?tr) (to-c ?tc) (start-dir ?sdir) (solution nil))
        =>
        (focus PATH)
)

;nella nuova implementazione, questo dovrebbe raccogliere i messaggi dall'agente e 
;fornire una lista di "azioni da fare" da ordinare poi in un piano
(defrule todo_from_message_to_agent      
        (declare (salience 10))
        
        ?g <- (msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        ?f <- (K-received-msg (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        
        (K-agent (step ?step) (content $?con) (free ?free) (waste ?waste))   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))
        (K-cell (pos-r ?mdisp-r) (pos-c ?mdisp-c) (contains MealDispenser))
        (K-cell (pos-r ?pdisp-r) (pos-c ?pdisp-c) (contains PillDispenser))        
        (K-cell (pos-r ?ddisp-r) (pos-c ?ddisp-c) (contains DessertDispenser))
        (K-cell (pos-r ?trash-r) (pos-c ?trash-c) (contains TrashBasket))


        ?h <- (todo-counter (id ?id))
        =>
        ;TODO: Considerazioni sullo stato dell'agente e sul planning
        ;(assert (to-action (step ?step) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc) (type_of_meal ?meal) (pills ?pills)))
        (if (eq ?request meal)
                then 
                (if (eq ?pills no)
                        then 
                        (assert (todo (id ?id) (request-time ?rqt) (step ?s) (sender ?P) (request meal) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                        (modify ?h (id (+ ?id 1)))
                        else
                        ;TODO pensare a come gestire before/after
                        (assert (todo (id ?id) (request-time ?rqt) (step ?s) (sender ?P) (request ?pills) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                        (assert (todo (id (+ ?id 1)) (request-time ?rqt) (step ?s) (sender ?P) (request meal) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                        (modify ?h (id (+ ?id 2)))
                )
                ; SPOSTATO IN MEAL EXPAND 
                ;se l'agente ha già caricato quel tipo di pasto richiesto
                ; (if (member$ ?meal $?con)
                ;         then 
                ;         (printout t "ok" clrf);OK
                ;         else 
                ;         (if (eq free 0)
                ;                 then ;MAKE SPACE
                ;                 else
                ;                 ;GET THE MEAL
                ;                 (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
                ;                 (modify ?h (id (+ ?id 1)))
                ;         )
                ; )
        )
         
        (if (eq ?request dessert)
                then
                (assert (todo (id ?id) (request-time ?rqt) (step ?s) (sender ?P) (request dessert) (goal_pos-r ?tr) (goal_pos-c ?tc)) )
                (modify ?h (id (+ ?id 1)))
        )

        ;una volta preso carico della richiesta con un todo, cancella il messaggio
        ;ATTENZIONE! bisogna essere certi di aver trattato la richiesta in qualche modo, ovvero
        ;che il TODO sia stato generato
        (retract ?g)
)
;nella nuova implementazione, questo dovrebbe raccogliere i messaggi dall'agente e 
;fornire una lista di "azioni da fare" da ordinare poi in un piano
(defrule todo_meal_expand  
        (declare (salience 10))        
        ?f <- (todo (expanded no) (request-time ?rqt) (step ?s) (sender ?P) (request meal))
        (K-cell (pos-r ?mdisp-r) (pos-c ?mdisp-c) (contains MealDispenser))
        (K-cell (pos-r ?pdisp-r) (pos-c ?pdisp-c) (contains PillDispenser))        
        (K-cell (pos-r ?ddisp-r) (pos-c ?ddisp-c) (contains DessertDispenser))
        (K-cell (pos-r ?trash-r) (pos-c ?trash-c) (contains TrashBasket))
        (K-agent (step ?step) (content $?con) (free ?free) (waste ?waste))   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert))



        ?h <- (todo-counter (id ?id))
        =>
        ;se l'agente ha già caricato quel tipo di pasto richiesto
        (if (member$ ?meal $?con)
                then ;OK
                (printout t "ok" clrf)
                (modify ?f (expanded yes))
                else 
                (if (eq free 0)
                        then 
                        ;MAKE SPACE
                        ;generazione dei todo per svuotare il load dell'agente e caricare un nuovo pranzo 
                        (modify ?f (expanded yes))
                        else
                        ;GET THE MEAL
                        (assert (todo (id ?id) (priority 9) (request-time ?rqt) (step ?s) (sender ?P) (request load_meal) (goal_pos-r ?mdisp-r) (goal_pos-c ?mdisp-c)) )
                        (modify ?h (id (+ ?id 1)))
                        (modify ?f (expanded yes))
                )
        )
)



;idea: calcolare subito i path necessari a tutti i TODO presenti. 
;NOTA: in realtà si potrebbe usare sempre l'euristica della manhattan distance.
;Senza un path e un costo di path, la strategy non può farsi un'idea del costo dell'azione complessiva.
(defrule path_generate
        (declare (salience 10))
        (K-agent (step ?step) (pos-r ?r) (pos-c ?c) (direction ?sdir))   
        ?g <- (todo (id ?todo-id) (goal_pos-r ?gr) (goal_pos-c ?gc))
        (not (path-request (id ?todo-id)))
        =>
        (assert (path-request (id ?todo-id) (from-r ?r) (from-c ?c) (to-r ?gr) (to-c ?gc) (start-dir ?sdir) (solution nil)))    
)

;Una volta calcolato il path all'obbiettivo del todo, si può fare una stima un po' più precisa del costo.
(defrule todo_cost_estimate
        (declare (salience 9))
        ?f <- (todo (id ?todo-id) (request ?req) (chosen_path nil))
        (path (id ?path-id) (obj-id ?todo-id) (cost ?cost1) (solution yes))
        (not (path (obj-id ?todo-id) (cost ?cost2&:(< ?cost2 ?cost1)) (solution yes)))
        =>
        (modify ?f (cost ?cost1) (chosen_path ?path-id))

)



;TODO: priority / scelta delle azioni da fare. Per ora è solo un fifo, prende il TODO più vecchio
(defrule strategy_choose_FIFO
        (declare (salience 8))
        ?f <- (todo (id ?id) (chosen_path ?path-id) (cost ?c1) (priority ?priority) (step ?s) (sender ?P) (request ?req))
        (not (todo (step ?s2&:(<= ?s2 ?s)) (priority ?pr2&:(< ?pr2 ?priority))  ))
        ; la clausola sul costo gli dà errore, al momento considera solo la FIFO (cost ?c2&:(< ?c2 ?c1))
        =>
        (printout t "execute todo " ?id)
        (assert (exec-todo (id ?id))) 
        (focus ACTION)

)