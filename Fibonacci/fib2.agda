fibo-from : ℕ -> ℕ -> ℕ -> ℕ
fibo-from m n 0               = m
fibo-from m n 1               = n
fibo-from m n (succ (succ k)) = fibo-from n (m + n) (succ k)

fast-fibo : ℕ -> ℕ
fast-fibo = fibo-from 0 1
