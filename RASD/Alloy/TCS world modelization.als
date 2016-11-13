//Helper signatures
enum Bool {True, False}

sig Position {
}

sig Plug {
}

sig Timestamp {
time:Int
}

//Actors
one sig ControlUnit {
contents: set SafeArea,
cars: set Car,
states: set State,
state: Car->one State,
statesCar:State->one Car,
users: set User,
pricePerMinute: Int
}{
state=~statesCar
}

fact {all u: User | u in ControlUnit.users
all c: Car | c in ControlUnit.cars
all st: State | st in ControlUnit.states
}
sig User {
userCode: Int
}{
userCode > 0
}

abstract sig Employee {
employeeId: Int,
}{
employeeId > 0
}

sig Manager extends Employee {
}

sig Operator extends Employee {
assignedtasks: set ServiceTask
}

one sig Administrator  extends Employee {

}



sig SafeArea {
borderPoints: set Position
}
sig PowerGridStation extends SafeArea{
}



sig Car {
carCode: Int
}{
carCode > 0
}

//Discounts and Overcharges
abstract sig PriceModifier{

}
abstract sig ChargePriceModifier extends PriceModifier{

}
one sig LowBatteryOvercharge extends ChargePriceModifier{

}
one sig FarFromPowerGridOvercharge extends PriceModifier{

}

one sig SufficientButteryDiscount extends ChargePriceModifier{

}
one sig CarLeftPlaggedDiscount extends ChargePriceModifier{

}
one sig PassagersDiscount extends PriceModifier{

}

//Fees
abstract sig Fee{

}
one sig NonSafeAreaParkingFee extends Fee{

}


//Car states
abstract sig State{
//car: one Car
}
sig ServiceTask extends State{
operator: lone Operator
}
sig Available extends State{
}
abstract sig Activity extends State{
user: one User
}

sig Reservation extends Activity{
startTime: one Timestamp
}

sig CodeRequest extends Activity{
//reservation:one Reservation
}

sig Ride extends Activity{
startTime: one Timestamp,
endTime: one Timestamp,
passQuantity: Int,
leftOutside:Bool,
PercentOfChargeLeft:one Int,
CarPluggedIn:one Bool,
Price:Int,
FeesToBeApplied: set Fee,
priceModifiersToBeApplied: set PriceModifier,
//ended: Bool
WithinSafeArea:lone SafeArea,
DistanceToPowerGridStation: Int//3 means 3 kilometers
}{
passQuantity>=0
Price>0
CarPluggedIn=True implies WithinSafeArea=PowerGridStation
}

//>>>>>Facts<<<<<

//Internal consistence constraints
fact {no disj a1,a2:Activity|a1.user=a2.user}
fact {all cu:ControlUnit, c1,c2:Car|c1->(c1.(cu.state))=c2->(c2.(cu.state)) implies c1=c2}
fact {all r:Ride|r.startTime.time<r.endTime.time}
fact {all o:Operator, st:ServiceTask|(st in o.assignedtasks)<=> (st.operator=o)}
fact {all r:Ride|0<=r.PercentOfChargeLeft and r.PercentOfChargeLeft<=7}//mapping of percents for alloy. 2 equals to 20 percent, 4 equals to 50 percent

//Identifiers uniqueness facts
fact userCodeUniqueness {
all u1,u2: User | (u1 != u2) => u1.userCode != u2.userCode
}

fact carCodeUniqueness {
all c1,c2: Car |(c1 != c2) => c1.carCode != c2.carCode
}

fact employeeIdUniqueness {
all e1,e2: Employee | (e1 != e2) => e1.employeeId != e2.employeeId
}

//Discounts, overcharges and fees facts. They will be applied if ride ends at that moment
fact{all r:Ride| (r.PercentOfChargeLeft<=2 and r.CarPluggedIn=False)<=> LowBatteryOvercharge in r.priceModifiersToBeApplied}
fact{all r:Ride| (r.PercentOfChargeLeft>=4  and r.CarPluggedIn=False)<=>SufficientButteryDiscount in r.priceModifiersToBeApplied}
fact{all r:Ride| r.CarPluggedIn=True<=>CarLeftPlaggedDiscount in r.priceModifiersToBeApplied}
fact{all r:Ride| r.passQuantity>=2<=>PassagersDiscount in r.priceModifiersToBeApplied}
fact{all r:Ride| r.WithinSafeArea=none<=>NonSafeAreaParkingFee in r.FeesToBeApplied}
fact{all r:Ride| r.DistanceToPowerGridStation>3<=>FarFromPowerGridOvercharge in r.priceModifiersToBeApplied}

//>>>>>Predicates<<<<<

// Predicate about changing state

pred changingState[cu, cu':ControlUnit, c: Car] {
c->(c.(cu.state))=c->(Available) implies cu'.state= cu.state - c->(c.(cu.state)) + c->(Reservation) or cu'.state= cu.state - c->(c.(cu.state))  + c->(ServiceTask)
c->(c.(cu.state))=c->(Reservation) implies cu'.state= cu.state - c->(c.(cu.state)) + c->(Available) or cu'.state= cu.state - c->(c.(cu.state))  + c->(CodeRequest) or cu'.state= cu.state - c->(c.(cu.state))  + c->(ServiceTask)
c->(c.(cu.state))=c->(CodeRequest) implies cu'.state= cu.state - c->(c.(cu.state)) + c->(Available) or cu'.state= cu.state - c->(c.(cu.state))  + c->(Ride) or cu'.state= cu.state - c->(c.(cu.state))  + c->(ServiceTask)
c->(c.(cu.state))=c->(Ride) implies cu'.state= cu.state - c->(c.(cu.state)) + c->(Available) or cu'.state= cu.state - c->(c.(cu.state))  + c->(ServiceTask)
c->(c.(cu.state))=c->(ServiceTask) implies cu'.state= cu.state - c->(c.(cu.state)) + c->(Available)
}


//>>>>>Assertions<<<<<
assert NoDoubleReservation{
no disj r1,r2:Reservation|r1.user=r2.user
}
check NoDoubleReservation

assert NoMultipleChargePriceModifiers{
no r:Ride, cpm1,cpm2:ChargePriceModifier| cpm1 in r.priceModifiersToBeApplied and  cpm2 in r.priceModifiersToBeApplied and cpm1!=cpm2
}
check NoMultipleChargePriceModifiers


pred show {
#Car = 5
#Ride= 2
some r: Ride | r.CarPluggedIn=True
}
run changingState for 5
run show for 5 
