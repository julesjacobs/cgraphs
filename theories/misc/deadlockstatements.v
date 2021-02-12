Nu:
deadlock(cfg) := niks kan stappen ∧ er is een thread die geen value is
              := ¬ (alle threads zijn een value ∨ exists a thread that can step)

deadlockfree(cfg) := for all cfg ->* cfg', ¬ deadlock(cfg')

typesafety(expr) := for all expr', such that expr ->* expr', expr' is a value ∨ expr' can step

safe(cfg) := for all cfg', cfg ->* cfg' -> all threads are (value | recv | can step)
deadlockfree(cfg) := for all cfg', cfg ->* cfg' -> all threads are value ∨ exists a thread that can step
leakfree(cfg) := for all cfg', cfg ->* cfg' -> all threads are unit -> buffers(cfg') = ∅


(let c' = fork(c => close(c))
 fun () => close(c')) : unit -> unit

(let c' = fork(c => recv(c); close(c))
 fun () => send(c',3); close(c')) : unit -> unit


Werkt niet:
deadlockfree(cfg) := ∀ thread ∈ cfg, ∀ cfg, cfg ->* cfg' -> exists cfg'', cfg' ->* cfg'' ∧ thread can step in cfg'

