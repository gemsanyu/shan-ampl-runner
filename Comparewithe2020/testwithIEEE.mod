#include testwithIEEE.run
#set

set F;  #CS(charging station) include dummy CS
set D0; #start_depot
set Dσ; #end_depot
set D :=D0 union Dσ;
set V; #customers
set Vplun :=V union F; #include customers and CS 
set Vall :=D union V union F; #set of network nodes
set Vplun0 :=V union D0 union F; #include customers and start deopt and CS
set Vplunend :=V union Dσ union F; #include customers and end deopt and CS
set V0 :=D0 union V; #Set of the depot node {0} and the customer nodes C
set Vσ :=Dσ union V; #Set of the customer nodes C and the final depot {σ}


#parameter
param n in V;            #number of customers
param t{i in Vall, j in Vall}>=0; # travel time between node i and j
param d{i in Vall, j in Vall}>=0; # distance between node i and j
param Cde;               # operational cost per unit distance of ECV
param Cdb;               # operational cost per unit distance of BSV
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



###################
param Ct;                # travel cost of ECV
param Cf;                # fixed acquisition cost of an ECV
param Cs;     			 # battery swap cost(BSS)
param Cr;				 # charging cost

#############

#decision variable
var x{i in Vall, j in Vall: i != j} binary;         # Vehicle from i to j
var xplun{i in Vplun, j in Vplun: i != j} binary;  				# BSV from i to j
var b{i in F} binary;           						# ECV choose to battery swap station it will be 1
var c{i in F} binary;           						# ECV choose to recharging station it will be 1
var y{i in Vall} >=0;               					# remaining battery level of ECV at node i
var yplun{Vplun} >=0;     	    								# remaining battery level of BSV at node i
var Y{i in F} >=0;                   				# remaining battery level of ECV from it depart at CS or BSS
var R{i in F}>=0;               # The recharging amount of ECV charged at CS node i
var u{i in Vall}>=0;            # remaining load on ECV at node i
var w{Vall} integer >= 0;  				   # number of remaining full batteries on BSV at node i
var A{i in Vall}>=0;            # EV arrival time at node i 
var Aplun{Vall}>=0;        				   # arrival time of BSV at node i
var a{i in Vall}>=0;            # customer service start time by EV at node i
var theta{Vplun}>=0;      			       # battery swap service start time by BSV at node i
var delta{Vall} binary;     			   # 1 if battery swapping at node i starts after [Ai,ei-zeta]


#the obj fun
#minimize TotalCost: 
    #CV * sum{i in D0, j in Vplun} x[i,j] +          			     # ECV fixed cost
    #CB * sum{i in F, j in V:i<>j} xplun[i,j] +       				 # BSV fixed cost
    #Cde * sum{i in Vall, j in Vall: i != j} d[i,j] * x[i,j] +        # ECV distance cost
    #Cdb * sum{i in Vplun, j in Vplun: i != j} d[i,j] * xplun[i,j] +  # BSV distance cost
    #Cb * (sum{i in F, j in Vplunend: i != j} b[i]* x[i,j] +sum{i in Vplun, j in V: i != j}xplun[i,j]);		# BSS/BSV battery swap cost

minimize TotalCost: 
    Cf * sum{i in D0, j in Vplun} x[i,j] +          			     # ECV fixed cost
    Ct * sum{i in Vall, j in Vall: i != j} x[i,j] * t[i,j] +        # ECV distance cost
    Cr * sum{i in F} c[i] * R[i] +
    Cs * sum{i in F, j in Vplunend: i != j} b[i]* x[i,j]; # BSV distance cost


#subject to
subject to limit2{i in V}:sum{j in Vplunend:i<>j}x[i,j]=1;
subject to limit3{i in F}:sum{j in Vplunend:i<>j}x[i,j]<=1;
subject to limit4{i in Vplun}:sum{j in Vplun0:i<>j}x[j,i] - sum{j in Vplunend:i<>j}x[i,j] = 0;
subject to limit5{i in V}:sum{j in Vplun:i<>j}xplun[j,i] - sum{j in Vplun:i<>j}xplun[i,j] = 0;

#subject to limit6{i in Vplun0, j in Vplunend:i<>j}:0 <= u[j] <= u[i] - m[i]*x[i,j] + C(1 - x[i,j]);
subject to limit6a{i in Vplun0, j in Vplunend:i<>j}:0 <= u[j];
subject to limit6b{i in Vplun0, j in Vplunend:i<>j}: 
    u[j] <= u[i] - m[i]*x[i,j] + C*(1 - x[i,j]);
    
subject to limit7{z in D0}:0 <= u[z] <= C;

#subject to limit8{i in Vplun, j in Vplun:i<>j}: 0 <= w[j] <= w[i] - xplun[i,j] + Qplun(1 - xplun[i,j]);
subject to limit8a{i in Vplun, j in Vplun:i<>j}: 0 <= w[j];
subject to limit8b{i in Vplun, j in Vplun:i<>j}: 
    w[j] <= w[i] - xplun[i,j] + Qplun*(1 - xplun[i,j]);
    
subject to limit9{z in D0}:0 <= w[z] <= Qplun;
subject to limit10{i in F}:Y[i] = c[i] * (y[i] + R[i]) + b[i]*Q;
subject to limit11{i in F}:0 <= Y[i] <= Q;
subject to limit12{j in F}:b[j] + c[j] <= 1;

#subject13要加D0限制倉庫出去到其他地方充電的電量限制
#subject to limit13{i in V, j in Vplunend:i != j}:0 <= y[j] <= (y[i] - h*d[i,j]*x[i,j] )*(1-sum{rho in Vplun: j in V  && rho != j}xplun[rho,j]) + Q*sum{rho in Vplun: j in V}xplun[rho,j];
subject to limit13a{i in D0 union V, j in Vplunend:i != j}:0 <= y[j] ;
subject to limit13b{i in D0 union V, j in Vplunend: i<>j}:
	y[j] <= (y[i] - h*d[i,j]*x[i,j])*(1-sum{rho in Vplun: j in V && rho != j}xplun[rho,j]) +
	Q*sum{rho in Vplun: j in V && rho != j}xplun[rho,j]+Q*(1-x[i,j]);

subject to limit14{j in V}:sum{rho in Vplun: j in V && rho != j}xplun[rho,j] <= 1;
subject to limit15{i in Vall}:0 <= y[i] <= Q;

#subject to limit16{i in F, j in Vplunend:i != j}:0 <= y[j] <= Y[i] - h*d[i,j]*x[i,j] + Q*sum {rho in  Vplun: j in V && rho != j} xplun[rho,j] + Q*(1 - x[i,j]);
subject to limit16a{i in F, j in Vplunend:i != j}:0 <= y[j];
subject to limit16b{i in F, j in Vplunend:i != j}:
	y[j] <= Y[i]- h*d[i,j]*x[i,j] + Q*sum {rho in  Vplun: j in V && rho != j} xplun[rho,j] + Q*(1 - x[i,j]);
	
#subject to limit17{i in Vplun, j in Vplun:i != j}:0 <= yplun[j] <= yplun[i] - hplun*d[i,j]*xplun[i,j] + W*(1 - xplun[i,j]);
subject to limit17a{i in Vplun, j in Vplun:i != j}:0 <= yplun[j];
subject to limit17b{i in Vplun, j in Vplun:i != j}:
	yplun[j] <= yplun[i] - hplun*d[i,j]*xplun[i,j] + W*(1 - xplun[i,j]);
subject to limit18{i in Vplun}:0 <= yplun[i]<= W;
subject to limit19{i in V}:a[i]=max(e[i],A[i]);
subject to limit20{i in V0, z in D0, j in Vplunend:i<>j}:
	a[i] + (t[i,j] + s[i])*x[i,j] + delta[i]*lamda - (l[z] + lamda)*(1 - x[i,j]) <= A[j];
subject to limit21{i in F, z in D0, j in Vplunend:i<>j}:
	A[i] + t[i,j]*x[i,j] + g*R[i]*c[i] + lamda*b[i] - l[z]*( 1 - x[i,j]) <= A[j];

#subject to limit22{i in V}:A[i] <= theta[i] <= (1 - delta[i])*(e[i] - lamda) + (1 - sum {j in Vplun} xplun[i,j] + delta[i])(l[i] + s[i]);
subject to limit22a{i in V}:A[i] <= theta[i];
subject to limit22b{i in V}:
	theta[i] <= (1 - delta[i])*(e[i] - lamda) + (1 - sum{j in Vplun:i<>j}xplun[i,j] + delta[i])*(l[i] + s[i]);

#subject to limit23{i in V}:a[i] + s[i] - (1 - delta[i])*(l[i] + s[i]) <= theta[i] <= a[i] + s[i] + (1 - delta[i])*(l[i] + s[i]);
subject to limit23a{i in V}:a[i] + s[i] - (1 - delta[i])*(l[i] + s[i]) <= theta[i];
subject to limit23b{i in V}:theta[i] <= a[i] + s[i] + (1 - delta[i])*(l[i] + s[i]);
subject to limit24{i in V}: Aplun[i] <= theta[i];
subject to limit25{i in Vplun, z in D0, j in Vplun:i<>j}:theta[i] + (t[i,j] + lamda)*xplun[i,j] - l[z]*(1 - xplun[i,j]) <= Aplun[j];
subject to limit26{i in Vall}:e[i] <= a[i] <= l[i];

subject to limit27{i in V}:sum {j in Vplunend:i<>j} h*d[i,j]*x[i,j] <= y[i];
subject to limit28{i in Vall}:e[i] <= A[i] <= l[i];
#subject to limit29{i in F}:b[i]=0;
#subject to limit30{i in F}:Q=y[i] + R[i];



subject to limit31{i in Vplun}:sum{j in Vplun:i<>j} xplun[i,j]=0;
