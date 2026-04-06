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
var ev_load{i in VF}>=0, <=C; # ev load upon departure (so in the last customer at least have 0, cannot be negative)

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
    sum{i in Vall: (i,j) in EV_ARCS} x[i,j] == is_cs_visited[j]
;

subject to cs_options {i in F}:
    choose_battery[i] + choose_charging[i] == is_cs_visited[i]
;

subject to ev_charge_amount_constraint {i in F}:
    ev_charge_amount[i] <= Q*choose_charging[i]
;

subject to ev_load_mtz_cust {i in VF, j in VF: (i,j) in EV_ARCS}:
    ev_load[j] <= ev_load[i] - m[j] + (C+m[j])*(1-x[i,j])
;

subject to ev_load_first_node {j in VF: (N0, j) in EV_ARCS}:
    ev_load[j] >= (C-m[j])*x[N0,j]
;


# we split arrival, start and departure time constraints for customer and stations
# and stations dont have start time, charging/swapping is done exactly on arrival
subject to ev_start_time1 {i in V}:
    ev_start[i] >= ev_arr[i]
;

subject to ev_start_time2 {i in V}: # this one actually already in variable domain
    ev_start[i] >= e[i]
;

subject to ev_departure_time_at_cust {i in V}:
    ev_dep[i] == ev_start[i] + s[i] + lamda*bsv_start_post_service[i]
;

subject to ev_departure_time_at_cs {i in F}:
    ev_dep[i] == ev_arr[i] + g*ev_charge_amount[i] + lamda*choose_battery[i]
;

subject to ev_time_flow {i in VF, j in VF: (i,j) in EV_ARCS}:
    ev_arr[j] >= ev_dep[i] + t[i,j] - (max_time+t[i,j])*(1-x[i,j])
;

subject to ev_arr_time_first_node {j in VF: (N0,j) in EV_ARCS}:
    ev_arr[j] >= t[N0, j]*x[N0, j]
;

subject to ev_dep_time_last_node {i in VF: (i,Nsig) in EV_ARCS}:
    ev_dep[i] <= x[i, Nsig]*(l[Nsig]-t[i, Nsig]) + max_time*(1 - x[i, Nsig])
;

# energy flow
subject to ev_energy_flow{i in VF, j in VF: (i,j) in EV_ARCS}:
    en_on_arr[j] <= en_on_dep[i] - h*d[i,j] + (Q+h*d[i,j])*(1-x[i,j])
;

subject to ev_energy_flow_first_node{j in VF: (N0,j) in EV_ARCS}:
    en_on_arr[j] <= Q - h*d[N0,j]*x[N0, j]
;

subject to ev_energy_flow_last_node{i in VF: (i, Nsig) in EV_ARCS}:
    en_on_dep[i] >= h*d[i,Nsig]*x[i,Nsig]
;

subject to ev_energy_cust_link1 {i in V}:
    en_on_dep[i] <= en_on_arr[i] + Q * is_bsv_destination[i];

subject to ev_energy_cust_link2 {i in V}:
    en_on_dep[i] >= en_on_arr[i] - Q * is_bsv_destination[i];

subject to ev_energy_cust_swap {i in V}:
    en_on_dep[i] >= Q * is_bsv_destination[i];

subject to ev_energy_cs_link1 {i in F}:
    en_on_dep[i] <= en_on_arr[i] + ev_charge_amount[i] + Q * choose_battery[i];

subject to ev_energy_cs_link2 {i in F}:
    en_on_dep[i] >= en_on_arr[i] + ev_charge_amount[i] - Q * choose_battery[i];

subject to ev_energy_cs_swap {i in F}:
    en_on_dep[i] >= Q * choose_battery[i];


# Symmetry Breaking Constraints for duplicate charging stations
subject to sbc_duplicate_cs_lex 
    {f in F_UNIQ, i in VF, j in F_NODES[f]: 
        j < max {j_ in F_NODES[f]} j_ and (i, j+1) in EV_ARCS}:
    
    sum {k in VF: k < i and (k,j) in EV_ARCS} x[k,j] >= x[i, j+1]
;