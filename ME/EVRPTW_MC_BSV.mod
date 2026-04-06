set F;  #CS(charging station) include duplicate CS
set F_UNIQ; #Unique CS only
set F_NODES {F_UNIQ};
set V; #customers
set D0; #start_depot set
set Dsig; #end_depot set
param N0 := min {i in D0} i; #start_depot
param Nsig := min {i in Dsig} i; #end_depot
set D := D0 union Dsig; # depot and dummy end depot
set Vall :=D union V union F; #all nodes
set VF := V union F;
set Vplun := V union F_UNIQ; #customer and unique CS only

set V_SELF_ARCS := setof {i in V} (i,i);
set F_SELF_ARCS := setof {f in F_UNIQ, i in F_NODES[f], j in F_NODES[f]} (i, j);
set SELF_ARCS := V_SELF_ARCS union F_SELF_ARCS;
set BACKWARD_ARCS := setof {i in Vall: i!=N0} (i,N0) union setof {i in Vall: i!=Nsig} (Nsig, i);
set EV_ARCS := (setof {i in Vall, j in Vall} (i,j)) diff (SELF_ARCS union BACKWARD_ARCS); 

set BSV_ARCS := (setof {i in Vplun, j in Vplun} (i,j)) diff SELF_ARCS;

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
param max_time:= max{i in Vall} l[i]; # the max time is latest due date of all nodes


#decision variables
# EV variables
var x{EV_ARCS} binary;  # Vehicle from i to j
var choose_battery{i in F} binary;   # ECV choose to battery swap station it will be 1
var choose_charging{i in F} binary;   # ECV choose to recharging station it will be 1
var is_cs_visited{i in F} binary;   # ECV choose to recharging station it will be 1
var en_on_arr{i in VF} >=0, <=Q;     # remaining battery level of ECV upon arrival at node i (pre charging & pre swapping if at CS)
var en_on_dep{i in VF} >=0, <=Q;     # battery level right before departure (after bsv swap, battery swap, or charging)
var ev_arr{i in VF} >=0; #ev arrival time
var ev_start{i in V} >=e[i], <=l[i]; #ev start service time at customer
var ev_dep{i in VF} >=0; #ev departure time
var ev_charge_amount{i in F}>=0, <=Q;
var ev_load{i in F}>=0, <=C-1; # ev load upon departure (so in the last customer at least have 0, cannot be negative)

# BSV variabels
var xplun{BSV_ARCS} binary; #bsv arc choices
var is_bsv_destination{i in V} binary; 
var bsv_start_pre_service{i in V} binary; 
var bsv_start_post_service{i in V} binary; 
var bsv_arr{i in V} >=0; #bsv arrival time
var bsv_start{i in V} >=0, <= l[i]+s[i]; #bsv start service time at customer
var bsv_dep{i in V} >=0, <=l[i]+s[i]+lamda; #bsv departure time
var bsv_load{i in V} >=0, <= Qplun-1; #bsv load upon departure (so in the last customer at least have 0, cannot be negative)
var bsv_energy{i in V} >=0, <= W; #arrival and departure is the same


# objective
minimize TotalCost:
    CV * sum{i in D0, j in VF} x[i,j] +          			     # ECV fixed cost
    CB * sum{i in F_UNIQ, j in V} xplun[i,j] +       				 # BSV fixed cost
    Ct * sum{(i,j) in EV_ARCS} t[i,j] * x[i,j] +        # ECV travel cost
    Ct * sum{(i,j) in BSV_ARCS} t[i,j] * xplun[i,j] +  # BSV travel cost
    Cr * sum{i in F} ev_charge_amount[i] + # recharging cost
    Cb * sum{i in F} choose_battery[i]  + #battery cost in CS
    Cb * sum{i in V} is_bsv_destination[i]; 	#battery cost calling BSV

# start with BSV constraints, seems easier
subject to bsv_flow_equality {j in V}:
    sum {i in Vplun: (i, j) in BSV_ARCS} xplun[i,j] == 
    sum {i in Vplun: (j, i) in BSV_ARCS} xplun[j,i]
;

subject to bsv_visit_at_most_once1 {j in V}:
    is_bsv_destination[j] == sum{i in Vplun: (i,j) in BSV_ARCS} xplun[i,j]
;

subject to bsv_select_service_time {i in V}:
    bsv_start_pre_service[i] + bsv_start_post_service[i] == is_bsv_destination[i]
;

subject to bsv_load_mtz {i in V, j in V: (i,j) in BSV_ARCS}:
    bsv_load[j] <= bsv_load[i] - 1 + (Qplun)*(1-xplun[i,j])
;

subject to bsv_load_mtz_first_cust {i in F_UNIQ, j in V: (i,j) in BSV_ARCS}:
    bsv_load[j] >= (Qplun - 1)*xplun[i,j]
;

subject to bsv_start_time_const1 {i in V}:
    bsv_start[i] >= bsv_arr[i]
;
subject to bsv_start_time_const2 {i in V}:
    bsv_start[i] >= ev_arr[i]
;
subject to bsv_dep_time_const {i in V}:
    bsv_dep[i] == bsv_start[i] + lamda
;

subject to bsv_start_time_const_pre1 {i in V}:
    bsv_start[i] + lamda <= e[i] + max_time*(1-bsv_start_pre_service[i])
;

subject to bsv_start_time_const_pre2 {i in V}:
    bsv_start[i] <= ev_arr[i] + max_time*(1-bsv_start_pre_service[i])
;

subject to bsv_start_time_const_pre3 {i in V}:
    bsv_start[i] >= ev_arr[i] - max_time*(1-bsv_start_pre_service[i])
;

subject to bsv_start_time_const_post1 {i in V}:
    bsv_start[i] >= ev_start[i] + s[i] - max_time*(1-bsv_start_post_service[i])
;

subject to bsv_start_time_const_post2 {i in V}:
    bsv_start[i] <= ev_start[i] + s[i] + max_time*(1-bsv_start_post_service[i])
;

subject to bsv_timeflow_cust {i in V, j in V: (i, j) in BSV_ARCS}:
    bsv_arr[j] >= bsv_dep[i] + t[i,j] - (max_time+t[i,j])*(1-xplun[i,j])
;

subject to bsv_timeflow_first_cust {i in F_UNIQ, j in V: (i,j) in BSV_ARCS}:
    bsv_arr[j] >= t[i,j]*xplun[i,j]
;

subject to bsv_timeflow_last_cust {i in V, j in F_UNIQ: (i,j) in BSV_ARCS}:
    bsv_dep[i] <= (l[j]-t[i,j])*xplun[i,j] + max_time*(1-xplun[i,j])
;

subject to bsv_energy_flow_cust {i in V, j in V: (i,j) in BSV_ARCS}:
    bsv_energy[j] <= bsv_energy[i] - hplun*d[i,j] + (W+hplun*d[i,j])*(1-xplun[i,j])
;

subject to bsv_energy_flow_first_cust {j in V, i in F_UNIQ: (i,j) in BSV_ARCS}:
    bsv_energy[j] <= W -hplun*d[i,j]*xplun[i,j]
;


# now EV constraints
subject to ev_must_visit_customer {j in V}:
    sum{i in Vall: (i,j) in EV_ARCS} x[i,j] == 1
;

subject to ev_flow_equality {j in VF}:
    sum{i in Vall: (i,j) in EV_ARCS} x[i,j] ==
    sum{i in Vall: (j,i) in EV_ARCS} x[j,i] 
;

subject to cs_visit_at_most_once {j in F}:
    sum{i in Vall: (i,j) in EV_ARCS} == is_cs_visited[j]
;

subject to cs_options {j in F}:
    choose_battery[j] + choose_charging[j] == is_cs_visited[j]
;

