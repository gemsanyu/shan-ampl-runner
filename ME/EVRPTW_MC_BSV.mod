set F;  #CS(charging station) include duplicate CS
set F_UNIQ; #Unique CS only
set F_NODES {F_UNIQ};
set V; #customers
set D0; #start_depot
set Dsig; #end_depot
set D := D0 union Dsig; # depot and dummy end depot
set Vall :=D union V union F; #all nodes
set Vplun := V union UNIQ_F; #customer and unique CS only

#parameters
param n in V;            #number of customers
param t{i in Vall, j in Vall}>=0; # travel time between node i and j
param d{i in Vall, j in Vall}>=0; # distance between node i and j
param CV;                # fixed acquisition cost of an ECV
param CB;                # fixed acquisition cost of a BSV
param Cb;     # battery swap cost(BSS/BSV)
param h;                 # energy consumption rate per unit distance of ECV
param hplun;             # energy consumption rate per unit distance of BSV
param e{Vall};         # earliest service time of customer i 
param l{Vall};         # latest service time of customer i
param s{Vall}>=0;      # service time at customer i
param m{Vall};         #demend of customer i
param Q;                 # ECV battery capacity
param Qplun;             # maximum number of batteries a BSV can carry
param C;                 # maximum payload of an ECV
param g;     			 # the recharging rate of ECV 
param lamda;             # time required for battery swapping on an ECV
param W;				 # BSV battery capacity
param Cr;				 # recharging cost
param Ct; 				 # travel cost


#decision variables
# EV
# var x{i in Vall, j in Vall: i != j} binary;         # Vehicle from i to j
# var b{i in F} binary;           # ECV choose to battery swap station it will be 1
# var c{i in F} binary;           # ECV choose to recharging station it will be 1
# var y{i in Vall} >=0;           # remaining battery level of ECV upon arrival at node i (pre charging & pre swapping if at CS)
# var yplun{Vplun} >=0;     	    # remaining battery level of BSV at node i
# var Y{i in F} >=0;              # remaining battery level of ECV right before it departs from CS or BSS
# var R{i in F}>=0;               # The recharging amount of ECV charged at CS node i
# var u{i in Vall}>=0;            # remaining load on ECV at node i
# var w{V} integer >= 0;  		# number of remaining full batteries on BSV at node i
# var A{i in Vall}>=0;            # EV arrival time at node i 
# var Aplun{Vall}>=0;        		# arrival time of BSV at node i
# var a{i in Vall}>=0;            # customer service start time by EV at node i
# var theta{Vplun}>=0;      		# battery swap service start time by BSV at node i
# var delta{Vall} binary;     	# 1 if battery swapping at node i starts after [Ai,ei-zeta]
# var xplun{i in Vplun, j in Vplun: i != j} binary;  	# BSV from i to j