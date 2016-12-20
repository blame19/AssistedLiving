;// STRATEGY

(defmodule STRATEGY (import MAIN ?ALL)   (export ?ALL) (import AGENT ?ALL))



;//_______Facts

;Fatto aggregato da passare ad Action 
; che contiene tutte le informazioni necessarie per soddisfare la richiesta, generando un piano
;ricordarsi che se necessario gli slot possono essere lasciati a null
(deftemplate to-action
        (slot step)
        (slot sender)
        ;request, per esempio meal e dessert (dall'ENV) o nostre personalizzate (trash, pills, goback, clean_table eccetera)
        ; eventualmente anche staccate (take_meal, take_dessert)
        (slot request)
        ;se la richista prevede la posizione (normale, di cella vuota)
        (slot pos-r) (slot pos-c)
        ;se la richiesta prevede la posizione di un tavolo o di un dispenser
        (slot t_pos-r) (slot t_pos-c)
        ;parametri opzionali
        (slot type_of_meal)
        (slot pills)
        (slot completed (allowed-values yes no))
)

;per chiedere a PATH di calcolare un percorso
(deftemplate path-request
        (slot id) (slot from-r) (slot from-c) (slot to-r) (slot to-c) (slot start-dir)
)


(deftemplate path-step (slot path-id) (slot node-id) (slot father-id) (slot node-r) (slot node-c) (slot direction))

;//_______Rules

(defrule TESTNEWPATH
        (declare (salience 16))
        (not (status (step 0)))
        =>
        (assert (path-request (id 0) (from-r 8) (from-c 6) (to-r 7) (to-c 2) (start-dir north) ))
        )

(defrule ask_path
        (path-request (id ?id) (from-r ?r) (from-c ?c) (to-r ?tr) (to-c ?tc) (start-dir ?sdir))
        =>
        (focus PATH)
)


(defrule request_from_message
        ?g <- (msg-to-agent (request-time ?rqt) (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        ?f <- (K-received-msg (step ?s) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc))
        (K-agent (step ?step) (content ?con) (free ?free) (waste ?waste))   
        (prescription (patient ?P) (meal ?meal) (pills ?pills) (dessert ?dessert)) 
        =>
        ;TODO: Considerazioni sullo stato dell'agente e sul planning
        (assert (to-action (step ?step) (sender ?P) (request ?request) (t_pos-r ?tr) (t_pos-c ?tc) (type_of_meal ?meal) (pills ?pills)))
        


)