attach("weight1_object.py")
attach("weight1_FC.py")
attach("weight1_decompose.py")
attach("weight1_forms.py")
attach("modp_space.py")

CM = load("DATA/CM_forms.1-600")
FC = weight_one_FC()
EXOTIC = {}
STURM = 20

def collect_weight_one_data(Nmin,Nmax):
	ans = []
	for N in range(Nmin,Nmax+1):
		G = DirichletGroup(N)
		Gs = G.galois_orbits()
		for chi in Gs:
			print "---------------------------------------------------------"
			print "Trying",chi[0].minimize_base_ring()
			A = wt1(chi[0].minimize_base_ring(),verbose=5)
			if len(A.exotic_forms()) > 0:
				ans += [A]
				print "Saving to file"
				f = open("DATA/weight1.data",'a')
				f.write('\n'+str(A)+'\n')
				f.write(str(A.exotic_forms())+str('\n'))
				f.close()
				print "*******************************************************"
				print ans
				print "*******************************************************"
			else:
				print "No forms"
	return ans
