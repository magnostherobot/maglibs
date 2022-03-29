ack : Nat -> Nat -> Nat
ack Z n = S n
ack (S m) Z = ack m 1
ack (S m) (S n) = ack m (ack (S m) n)
