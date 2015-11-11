program pd_example

integer, dimension (1 : 12) :: A, C

A = (/ (I, I = 1, 12) /)
C = A + 1

print *, C

end program pd_example
