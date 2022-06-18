-------------------- MODULE KF6009IsleOfSodorAssessment --------------------
EXTENDS Sequences, Integers, FiniteSets, TLC \** Modules required for the specification to operate correctly.
VARIABLE Thomas, ThomasCarriage, FfarquharStations, Gordon, GordonCarriage, SodorStations \** Variables used within Spec.
vars == <<Thomas, ThomasCarriage, FfarquharStations, Gordon, GordonCarriage, SodorStations>> \** Variables to be used within Temporal Logic.


FfarquharLine == <<"Knapford","Elsbridge","Ffarquhar">> \**Sets the FfarquharLine to be used by Thomas
PassengerFfarquhar == [source : DOMAIN FfarquharLine, destination : DOMAIN FfarquharLine] \** Sets the Passengers used on the FfarquharLine.

SodorLine == <<"Barrow-in-Furness","Knapford","Tidmouth">> \** Sets the SodorLine to be used by Gordon
PassengerSodor == [source : DOMAIN SodorLine, destination : DOMAIN SodorLine] \** Sets the Passengers used on the SodorLine

TypeOK ==
    /\ Thomas \in [Location : DOMAIN FfarquharLine, Direction : BOOLEAN, DoorsOpen: BOOLEAN, DoneLoad: BOOLEAN] \** Declares the attributes related to Thomas.
    /\ ThomasCarriage \subseteq PassengerFfarquhar \** The Carriage used by Thomas is a subset of the Passengers on the Ffarquhar Line.
    /\ DOMAIN FfarquharStations = DOMAIN FfarquharLine \** The stations on the Ffarquhar line is the same as the sequence assigned to FfarquharLine.
    /\ \A i \in DOMAIN FfarquharStations : FfarquharStations[i] \subseteq PassengerFfarquhar \** All the individuals at the Ffarquhar stations are possible Passengers. 
    
    /\ Gordon \in [Location : DOMAIN SodorLine, Direction : BOOLEAN, DoorsOpen: BOOLEAN, DoneLoad: BOOLEAN] \** Declares the attributes related to Gordon.
    /\ GordonCarriage \subseteq PassengerSodor \** The Carriage used by Gordon is a subset of the Passengers on the Sodorline.
    /\ DOMAIN SodorStations = DOMAIN SodorLine \** The stations on the Sodor line is the same as the sequence in the SodorLine sequence.
    /\ \A i \in DOMAIN SodorStations : SodorStations[i] \subseteq PassengerSodor \** All the individuals at the SodorStation are possible Passengers.

Init == 
    /\ Thomas = [Location |-> 1, Direction |-> TRUE, DoorsOpen |-> FALSE, DoneLoad |-> FALSE] \** Initialises Thomas, starting at Knapford going towars ffarquhar, doors shut and not unloading.
    /\ ThomasCarriage = {} \** Thomas' Carriage starts the trip empty.
    /\ FfarquharStations = [pl \in DOMAIN FfarquharLine |-> [source : {pl}, destination : DOMAIN FfarquharLine \ {pl}]] \** There is a passenger at every station with a destination at every station, except for one whos starting location is the same as their destination.
    
    /\ Gordon = [Location |-> 1, Direction |-> TRUE, DoorsOpen |-> FALSE, DoneLoad |-> FALSE] \** Initialises Gordon, starting at Barrow-in-Furness going towards Tidmouth, doors shut and not unloading.
    /\ GordonCarriage = {} \** Gordon's Carriage starts the trip empty.
    /\ SodorStations = [pl \in DOMAIN SodorLine |-> [source : {pl}, destination : DOMAIN SodorLine \ {pl}]] \** There is a passenger at every station with a destination at every station, except for one whos starting location is the same as their destination.
    
    
    
\**HANDLES THE FUNCTIONS FOR THOMAS, INCLUDING MOVEMENT,LOADING AND UNLOADING.


GetOffThomas == \** Functionality for passengers to disembark from Thomas upon reaching their destination.
    /\ Thomas.DoorsOpen = TRUE \** Thomas' doors are set to be open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is allowing loading and unloading.
    /\ \E p \in ThomasCarriage : \** There exists a passenger on Thomas that wishes to get off.
        /\ p.destination = Thomas.Location \** The passenger's destination is where Thomas is currently at.
        /\ ThomasCarriage' = ThomasCarriage \ {p} \** Remove the Passenger from the Carriage, don't add them back to the Station stock.
    /\ UNCHANGED FfarquharStations \** The Station is not impacted by this change.
    /\ UNCHANGED Thomas \**Thomas is not affected or altered.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage  \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
        
GetOnThomas == \** Functionality for Passengers to enter Thomas' Carriage upon him arriving at their station.
    /\ Thomas.DoorsOpen = TRUE \** Thomas' doors are set to be open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is allowing loading and unloading.
    /\ \E p \in FfarquharStations[Thomas.Location] : \** There exists a passenger at the platform which want to get onto Thomas.
        /\ p.destination # Thomas.Location \** The destination of the passenger is not Thomas' current location.
        /\ ThomasCarriage' = ThomasCarriage \cup {p} \** Add the passenger to Thomas' carriage.
        /\ FfarquharStations' = [l \in DOMAIN FfarquharStations |-> \** Code will remove the Passenger from the FfarquharStations list, meaning they are only present within Thomas' Carriage.
                            IF l = Thomas.Location \** If l is Thomas' current location (The current station).
                            THEN FfarquharStations[l] \ {p} \** Remove the passenger from the station in question.
                            ELSE FfarquharStations[l]] \** Else do nothing.
    /\ UNCHANGED Thomas \** Thomas is not affected or altered.
    /\ UNCHANGED Gordon \** Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.

InterchangeThomas == \** This functionality is used for passengers to swap stations at Knapford from the Ffarquhar line to the Sodor line.
    /\ Thomas.DoorsOpen = TRUE \** Thomas' doors are set to be open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is allowing loading.
    /\ Thomas.Location = 1 \** Thomas' location is 1 (Knapford).
    /\ \E p \in ThomasCarriage : \** There exists a passenger in Thomas' Carriage
        /\ p.destination = 1 \** Who's destination is 1 (Knapford).
        /\ ThomasCarriage' = ThomasCarriage \ {p} \** Remove the Passenger from Thomas' Carriage.
        /\ SodorStations' = [l \in DOMAIN FfarquharStations |->  \** Will add the Passenger to the SodorLine, firstly states variable l is within the current Ffarquhar Line.
                            IF l = Thomas.Location \** If l is Thomas' current location (Knapford).
                            THEN SodorStations[l] \cup {p} \** Add the passenger to the Sodor line.
                            ELSE SodorStations[l]] \** Otherwise do nothing. 
    /\ UNCHANGED Thomas \**Thomas is unaffected.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.
     
OpenThomasDoors == \** Functionality to open Thomas' doors upon reaching a station.
    /\ Thomas.DoorsOpen = FALSE \** Thomas' doors are set to be closed.
    /\ Thomas.DoneLoad = FALSE \** Thomas is not unloading.
    /\ Thomas' = [Thomas EXCEPT !.DoorsOpen = ~@, !.DoneLoad = TRUE] \** This opens the doors and allows for unloading and loading to occur.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.

CloseThomasDoors == \** Functionality to close Thomas' doors when finished with passengers.
    /\ Thomas.DoorsOpen = TRUE \** Thomas' doors are set to be open.
    /\ Thomas' = [Thomas EXCEPT !.DoorsOpen = ~@] \** Set Thomas' doors to close.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.
    /\ ~ENABLED GetOffThomas \** Passengers cannot get off the train when the doors are closed.
    /\ ~ENABLED GetOnThomas \** Passengers cannot get on the train when the doors are closed.
    /\ ~ENABLED InterchangeThomas \** Passengers cannot get off at the Interchange when the doors are closed.
    
FfarquharTurn == \** Functionality to turn Thomas when reaching Ffarquhar.
    /\ Thomas.Location = Len(FfarquharLine) \** Thomas' location is the end of the Ffarquhar line (Ffarquhar).
    /\ Thomas.Direction = TRUE \** Thomas is going towards Ffarquhar.
    /\ Thomas.DoorsOpen = FALSE \** The doors are not open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is currently allowing loading and unloading.
    /\ Thomas' =[Thomas EXCEPT !.Direction = FALSE]\** Change Thomas' direction to be towards Knapford.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.
    
KnapfordTurn == \** Functionality to turn Thomas when reaching Knapford.
    /\ Thomas.Location = 1 \** Thomas' location is the start of the Ffarquhar line (Knapford).
    /\ Thomas.Direction = FALSE \** Thomas is heading towards Knapford.
    /\ Thomas.DoorsOpen = FALSE \** Thomas' doors are not open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is not loading or unloading.
    /\ Thomas' =[Thomas EXCEPT !.Direction = TRUE] \** Change Thomas' direction to be towards Ffarquhar.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.

GoForwardsThomas == \** Functionality to move Thomas through all stations going towards Ffarquhar.
    /\ Thomas.Direction = TRUE \**Thomas will head towards Ffarquhar.
    /\ Thomas.Location < Len(FfarquharLine) \** Thomas will go through each station up to Ffarquhar, to allow for turning.
    /\ Thomas.DoorsOpen = FALSE \** Thomas' doors are not open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is not loading or unloading.
    /\ Thomas' = [Thomas EXCEPT !.Location = @+1, !.DoneLoad = FALSE] \** Thomas will move through the line back to Ffarquhar one by one, not unloading during this time.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.

GoBackwardsThomas == \** Functionality to move Thomas through all stations going towards Knapford.
    /\ Thomas.Direction = FALSE \**Thomas will head towards Knapford.
    /\ Thomas.Location > 1 \** Thomas will go through each station up to Knapford, to allow for turning.
    /\ Thomas.DoorsOpen = FALSE \** Thomas' doors are not open.
    /\ Thomas.DoneLoad = TRUE \** Thomas is not loading or unloading.
    /\ Thomas' = [Thomas EXCEPT !.Location = @-1, !.DoneLoad = FALSE] \** Thomas will move back down the Ffarquhar line, stopping at each station one by one. He will not unload during this move.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar stations are not altered.
    
    
    
\**HANDLES THE FUNCTIONS FOR GORDON, INCLUDING MOVEMENT,LOADING AND UNLOADING.    


GetOffGordon == \** Functionality for Passengers to disembark from Gordon when he reaches their destination.
    /\ Gordon.DoorsOpen = TRUE \** Gordon's doors are set to be open.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ \E p \in GordonCarriage : \** There exists a passenger on Gordon that wishes to get off.
        /\ p.destination = Gordon.Location \** The passenger's destination is where gordon is currently at.
        /\ GordonCarriage' = GordonCarriage \ {p} \** Remove the Passenger from the Carriage, don't add them back to the Station stock.
    /\ UNCHANGED Gordon \**Gordon is not affected or altered.
    /\ UNCHANGED Thomas \** Thomas is not affected.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
        
GetOnGordon == \** Functionality for Passengers to get on Gordon when he reaches their station.
    /\ Gordon.DoorsOpen = TRUE \** Gordon's doors are set to be open.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ \E p \in SodorStations[Gordon.Location] : \** There exists a passenger at the platform which wants to get onto Gordon.
        /\ p.destination # Gordon.Location \** The destination of the passenger is not Gordon's current location.
        /\ GordonCarriage' = GordonCarriage \cup {p} \** Add the passenger to Gordon's carriage.
        /\ SodorStations' = [l \in DOMAIN SodorStations |-> \** Code will remove the Passenger from the Sodor Stations list, meaning they are only present within Gordon's Carriage.
                            IF l = Gordon.Location \** If l is equal to Gordon's current location (The Passengers station).
                            THEN SodorStations[l] \ {p} \** Remove the Passenger form the Sodor Station list.
                            ELSE SodorStations[l]] \** Otherwise do nothing.
    /\ UNCHANGED Gordon \** Gordon is not affected or altered.
    /\ UNCHANGED Thomas \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.
    
InterchangeGordon == \** This functionality is used for swapping stations from the Sodor line to the Ffarquhar line.
    /\ Gordon.DoorsOpen = TRUE \** Gordon's doors are set to be open.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ Gordon.Location = 2 \** Gordon's current locations is 2 (Knapford).
    /\ \E p \in GordonCarriage : \** There exists a Passnger in Gordon's Carriage.
        /\ p.destination = 2 \** Who's destination is Knapford.
        /\ GordonCarriage' = GordonCarriage \ {p} \** Remove this Passenger from the Carriage.
        /\ FfarquharStations' = [l \in DOMAIN SodorStations |-> \** Add this passenger to Ffarquhar station list, checks the location of Gordon within the Sodor line.
                            IF l = Gordon.Location \** If l is equal to gordon's current location (Knapford).
                            THEN FfarquharStations[l] \cup {p} \** Add the Passenger to the Ffarquhar line.
                            ELSE FfarquharStations[l]] \** Otherwise ignore.
    /\ UNCHANGED Thomas \** Thomas is not affected or altered.
    /\ UNCHANGED Gordon \** Gordon is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.

OpenGordonDoors == \** Functionality for opening Gordon's doors.
    /\ Gordon.DoorsOpen = FALSE \** Gordon's doors are set to be closed.
    /\ Gordon.DoneLoad = FALSE \** Gordon is not unloading
    /\ Gordon' = [Gordon EXCEPT !.DoorsOpen = ~@, !.DoneLoad = TRUE] \** This opens the doors and allows for unloading and loading to occur.
    /\ UNCHANGED Thomas \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.
    
CloseGordonDoors == \** Functionality to Close Gordon's doors.
    /\ Gordon.DoorsOpen = TRUE \** Gordon's doors are set to be open.
    /\ Gordon' = [Gordon EXCEPT !.DoorsOpen = ~@] \** Set Gordon's doors to close.
    /\ UNCHANGED Thomas \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.
    /\ ~ENABLED GetOffGordon \** Passengers cannot get off of Gordon when the doors are closed.
    /\ ~ENABLED GetOnGordon \** Passengers cannot get onto Gordon when the doors are closed.
    /\ ~ENABLED InterchangeGordon \** Passengers cannot get off of Gordon to change stations when the doors are closed.
    
TidmouthTurn == \** Turns the train when reaching Tidmouth.
    /\ Gordon.Location = Len(SodorLine) \** Gordon's location is the end of the Sodor line (Tidmouth).
    /\ Gordon.Direction = TRUE \** Gordon is going towards Tidmouth.
    /\ Gordon.DoorsOpen = FALSE \** Gordon's doors are set to be closed.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ Gordon' =[Gordon EXCEPT !.Direction = FALSE]\** Change Gordon's direction to be towards Barrow-in-Furness.
    /\ UNCHANGED Thomas \** \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.

BarrowTurn == \** Turns the train when reaching Barrow-in-furness.
    /\ Gordon.Location = 1 \** \** Gordon's location is the start of the Sodor line (Barrow-in-furness).
    /\ Gordon.Direction = FALSE \** Gordon is heading towards Barrow-in-furness.
    /\ Gordon.DoorsOpen = FALSE \** Gordon's doors are set to be closed.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ Gordon' =[Gordon EXCEPT !.Direction = TRUE] \** Change Gordon's direction to be towards Tidmouth.
    /\ UNCHANGED Thomas \** \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.

GoForwardsGordon == \** Functionality to move Gordon forward towards Tidmouth.
    /\ Gordon.Direction = TRUE \**Gordon will head towards Tidmouth.
    /\ Gordon.Location < Len(SodorLine)\** Gordon will go through each station up to Tidmouth, to allow for turning.
    /\ Gordon.DoorsOpen = FALSE \** Gordon's doors are set to be closed.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ Gordon' = [Gordon EXCEPT !.Location = @+1, !.DoneLoad = FALSE] \** Gordon will move through the line towards Tidmouth, not unloading during this time.
    /\ UNCHANGED Thomas \** \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.

GoBackwardsGordon == \** Functionality to move Gordon back towards Barrow-in-furness.
    /\ Gordon.Direction = FALSE \** Gordon will head towards Barrow-in-furness.
    /\ Gordon.Location > 1 \** Gordon will go through each station up to Barrow-in-furness, to allow for turning.
    /\ Gordon.DoorsOpen = FALSE \** Gordon's doors are set to be closed.
    /\ Gordon.DoneLoad = TRUE \** Gordon is allowing loading and unloading.
    /\ Gordon' = [Gordon EXCEPT !.Location = @-1, !.DoneLoad = FALSE] \** Gordon will move through the line back to Barrow-in-furness, not unloading during this time.
    /\ UNCHANGED Thomas \** \** Thomas is not affected or altered.
    /\ UNCHANGED ThomasCarriage \** The Passengers within Thomas' carriage are not affected.
    /\ UNCHANGED GordonCarriage \** The Passengers within Gordon's carriage are not affected.
    /\ UNCHANGED SodorStations \** The Passengers at the Sodor Stations are not altered.
    /\ UNCHANGED FfarquharStations \** The Passengers at the Ffarquhar Stations are not affected.


Next ==
\/OpenThomasDoors
\/CloseThomasDoors
\/OpenGordonDoors
\/CloseGordonDoors
\/FfarquharTurn
\/KnapfordTurn
\/TidmouthTurn
\/BarrowTurn
\/GoForwardsThomas
\/GoBackwardsThomas
\/GoForwardsGordon
\/GoBackwardsGordon
\/GetOffThomas
\/GetOnThomas
\/GetOnGordon
\/GetOffGordon
\/InterchangeThomas
\/InterchangeGordon


\**Sets the fairness of each function within the specification.
Fairness == 
/\ SF_vars(OpenThomasDoors)
/\ SF_vars(CloseThomasDoors)
/\ SF_vars(OpenGordonDoors)
/\ SF_vars(CloseGordonDoors)
/\ WF_vars(FfarquharTurn)
/\ WF_vars(KnapfordTurn)
/\ WF_vars(TidmouthTurn)
/\ WF_vars(BarrowTurn)
/\ WF_vars(GoForwardsThomas)
/\ WF_vars(GoBackwardsThomas)
/\ WF_vars(GoForwardsGordon)
/\ WF_vars(GoBackwardsGordon)
/\ SF_vars(GetOffThomas)
/\ SF_vars(GetOnThomas)
/\ SF_vars(GetOnGordon)
/\ SF_vars(GetOffGordon)
/\ SF_vars(InterchangeThomas)
/\ SF_vars(InterchangeGordon)

Spec == Init /\ [][Next]_vars /\ Fairness

AllPassengersArriveThomas == \** Ensures that all Passengers on the Ffarquhar Line will eventually reach their destination.
    \A p \in PassengerFfarquhar : (p \in FfarquharStations[p.source]) ~> (p \in FfarquharStations[p.destination])
    
AllPassengersArriveGordon == \** Ensures that all Passengers on the Sodor Line will eventually reach their destination.
    \A p \in PassengerSodor : (p \in SodorStations[p.source]) ~> (p \in SodorStations[p.destination])

=============================================================================
\* Modification History
\* Last modified Tue May 10 17:42:50 BST 2022 by Ethan
\* Created Tue May 10 17:41:54 BST 2022 by Ethan
