from sympy import *

h = symbols('h',positive=true)

A = Matrix([[1 - h**2/2, -h/2*(2-h**2/2)],[h , 1-h**2/2]])

print("transition matrix")
print(A)
print("\n")


ATA = A.adjoint()*A


print("gram matrix")
print(simplify(ATA))
print("\n")


v1 = ATA.eigenvects()[0][2][0]
v2 = ATA.eigenvects()[1][2][0]


print("Eigenvector matrix ATA")
u1 = (1/v1.norm())*v1
u2 = (1/v2.norm())*v2
U = u1.row_join(u2)
print(simplify(U))
print("\n")


print("Eigenvalue matrix ATA")
print(simplify(U.T*ATA*U))



print("Eigenvector matrix A")
P,D = A.diagonalize()

print(simplify(P))

print("\n")


print("Eigenvalue matrix A")
print(simplify(D))


print("\n")


print("Eigenvector matrix A inv")
print(simplify(P.inv()))

print(simplify(P.inv() * P))



h = 1/32
v1 = Matrix([[-sqrt(h**2 - 4)/2], [1]])
v2 = Matrix([[sqrt(h**2 - 4)/2], [1]])

print(0.5*v1.norm()+0.5*v2.norm())
