node(1).
node(2).
node(3).
node(4).
node(5).
node(6).
node(7).
node(8).
node(9).
link(2,6).
link(6,2).
link(3,5).
link(5,3).
link(3,6).
link(6,3).
colour(red0).
colour(green0).
colour(blue0).
colour(yellow0).
colour(cyan0).
colours(green0,red0).
colours(blue0,red0).
colours(cyan0,red0).
colours(blue0,green0).
colours(cyan0,green0).
colours(red0,yellow0).
colours(green0,yellow0).
colours(blue0,yellow0).
colours(cyan0,yellow0).
colours(blue0,cyan0).
notnext(blue0,red0).
notnext(cyan0,red0).
notnext(blue0,green0).
notnext(green0,yellow0).
notnext(blue0,yellow0).
notnext(cyan0,yellow0).
next(green0,red0).
next(cyan0,green0).
next(red0,yellow0).
next(blue0,cyan0).
later(red0).
later(green0).
later(yellow0).
later(cyan0).
index(blue0,1).
index(cyan0,2).
index(green0,3).
index(red0,4).
index(yellow0,5).
chosenColour(1,blue0):-not notChosenColour(1,blue0).
chosenColour(2,blue0):-not notChosenColour(2,blue0).
chosenColour(3,blue0):-not notChosenColour(3,blue0).
chosenColour(4,blue0):-not notChosenColour(4,blue0).
chosenColour(5,blue0):-not notChosenColour(5,blue0).
chosenColour(6,blue0):-not notChosenColour(6,blue0).
chosenColour(7,blue0):-not notChosenColour(7,blue0).
chosenColour(8,blue0):-not notChosenColour(8,blue0).
chosenColour(9,blue0):-not notChosenColour(9,blue0).
chosenColour(2,cyan0):-not notChosenColour(2,cyan0).
chosenColour(3,cyan0):-not notChosenColour(3,cyan0).
chosenColour(4,cyan0):-not notChosenColour(4,cyan0).
chosenColour(5,cyan0):-not notChosenColour(5,cyan0).
chosenColour(6,cyan0):-not notChosenColour(6,cyan0).
chosenColour(7,cyan0):-not notChosenColour(7,cyan0).
chosenColour(8,cyan0):-not notChosenColour(8,cyan0).
chosenColour(9,cyan0):-not notChosenColour(9,cyan0).
chosenColour(3,green0):-not notChosenColour(3,green0).
chosenColour(4,green0):-not notChosenColour(4,green0).
chosenColour(5,green0):-not notChosenColour(5,green0).
chosenColour(6,green0):-not notChosenColour(6,green0).
chosenColour(7,green0):-not notChosenColour(7,green0).
chosenColour(8,green0):-not notChosenColour(8,green0).
chosenColour(9,green0):-not notChosenColour(9,green0).
chosenColour(4,red0):-not notChosenColour(4,red0).
chosenColour(5,red0):-not notChosenColour(5,red0).
chosenColour(6,red0):-not notChosenColour(6,red0).
chosenColour(7,red0):-not notChosenColour(7,red0).
chosenColour(8,red0):-not notChosenColour(8,red0).
chosenColour(9,red0):-not notChosenColour(9,red0).
chosenColour(5,yellow0):-not notChosenColour(5,yellow0).
chosenColour(6,yellow0):-not notChosenColour(6,yellow0).
chosenColour(7,yellow0):-not notChosenColour(7,yellow0).
chosenColour(8,yellow0):-not notChosenColour(8,yellow0).
chosenColour(9,yellow0):-not notChosenColour(9,yellow0).
notChosenColour(2,blue0):-chosenColour(2,cyan0).
notChosenColour(3,blue0):-chosenColour(3,cyan0).
notChosenColour(4,blue0):-chosenColour(4,cyan0).
notChosenColour(5,blue0):-chosenColour(5,cyan0).
notChosenColour(6,blue0):-chosenColour(6,cyan0).
notChosenColour(7,blue0):-chosenColour(7,cyan0).
notChosenColour(8,blue0):-chosenColour(8,cyan0).
notChosenColour(9,blue0):-chosenColour(9,cyan0).
notChosenColour(3,blue0):-chosenColour(3,green0).
notChosenColour(4,blue0):-chosenColour(4,green0).
notChosenColour(5,blue0):-chosenColour(5,green0).
notChosenColour(6,blue0):-chosenColour(6,green0).
notChosenColour(7,blue0):-chosenColour(7,green0).
notChosenColour(8,blue0):-chosenColour(8,green0).
notChosenColour(9,blue0):-chosenColour(9,green0).
notChosenColour(4,blue0):-chosenColour(4,red0).
notChosenColour(5,blue0):-chosenColour(5,red0).
notChosenColour(6,blue0):-chosenColour(6,red0).
notChosenColour(7,blue0):-chosenColour(7,red0).
notChosenColour(8,blue0):-chosenColour(8,red0).
notChosenColour(9,blue0):-chosenColour(9,red0).
notChosenColour(5,blue0):-chosenColour(5,yellow0).
notChosenColour(6,blue0):-chosenColour(6,yellow0).
notChosenColour(7,blue0):-chosenColour(7,yellow0).
notChosenColour(8,blue0):-chosenColour(8,yellow0).
notChosenColour(9,blue0):-chosenColour(9,yellow0).
notChosenColour(2,cyan0):-chosenColour(2,blue0).
notChosenColour(3,cyan0):-chosenColour(3,blue0).
notChosenColour(4,cyan0):-chosenColour(4,blue0).
notChosenColour(5,cyan0):-chosenColour(5,blue0).
notChosenColour(6,cyan0):-chosenColour(6,blue0).
notChosenColour(7,cyan0):-chosenColour(7,blue0).
notChosenColour(8,cyan0):-chosenColour(8,blue0).
notChosenColour(9,cyan0):-chosenColour(9,blue0).
notChosenColour(3,cyan0):-chosenColour(3,green0).
notChosenColour(4,cyan0):-chosenColour(4,green0).
notChosenColour(5,cyan0):-chosenColour(5,green0).
notChosenColour(6,cyan0):-chosenColour(6,green0).
notChosenColour(7,cyan0):-chosenColour(7,green0).
notChosenColour(8,cyan0):-chosenColour(8,green0).
notChosenColour(9,cyan0):-chosenColour(9,green0).
notChosenColour(4,cyan0):-chosenColour(4,red0).
notChosenColour(5,cyan0):-chosenColour(5,red0).
notChosenColour(6,cyan0):-chosenColour(6,red0).
notChosenColour(7,cyan0):-chosenColour(7,red0).
notChosenColour(8,cyan0):-chosenColour(8,red0).
notChosenColour(9,cyan0):-chosenColour(9,red0).
notChosenColour(5,cyan0):-chosenColour(5,yellow0).
notChosenColour(6,cyan0):-chosenColour(6,yellow0).
notChosenColour(7,cyan0):-chosenColour(7,yellow0).
notChosenColour(8,cyan0):-chosenColour(8,yellow0).
notChosenColour(9,cyan0):-chosenColour(9,yellow0).
notChosenColour(3,green0):-chosenColour(3,blue0).
notChosenColour(4,green0):-chosenColour(4,blue0).
notChosenColour(5,green0):-chosenColour(5,blue0).
notChosenColour(6,green0):-chosenColour(6,blue0).
notChosenColour(7,green0):-chosenColour(7,blue0).
notChosenColour(8,green0):-chosenColour(8,blue0).
notChosenColour(9,green0):-chosenColour(9,blue0).
notChosenColour(3,green0):-chosenColour(3,cyan0).
notChosenColour(4,green0):-chosenColour(4,cyan0).
notChosenColour(5,green0):-chosenColour(5,cyan0).
notChosenColour(6,green0):-chosenColour(6,cyan0).
notChosenColour(7,green0):-chosenColour(7,cyan0).
notChosenColour(8,green0):-chosenColour(8,cyan0).
notChosenColour(9,green0):-chosenColour(9,cyan0).
notChosenColour(4,green0):-chosenColour(4,red0).
notChosenColour(5,green0):-chosenColour(5,red0).
notChosenColour(6,green0):-chosenColour(6,red0).
notChosenColour(7,green0):-chosenColour(7,red0).
notChosenColour(8,green0):-chosenColour(8,red0).
notChosenColour(9,green0):-chosenColour(9,red0).
notChosenColour(5,green0):-chosenColour(5,yellow0).
notChosenColour(6,green0):-chosenColour(6,yellow0).
notChosenColour(7,green0):-chosenColour(7,yellow0).
notChosenColour(8,green0):-chosenColour(8,yellow0).
notChosenColour(9,green0):-chosenColour(9,yellow0).
notChosenColour(4,red0):-chosenColour(4,blue0).
notChosenColour(5,red0):-chosenColour(5,blue0).
notChosenColour(6,red0):-chosenColour(6,blue0).
notChosenColour(7,red0):-chosenColour(7,blue0).
notChosenColour(8,red0):-chosenColour(8,blue0).
notChosenColour(9,red0):-chosenColour(9,blue0).
notChosenColour(4,red0):-chosenColour(4,cyan0).
notChosenColour(5,red0):-chosenColour(5,cyan0).
notChosenColour(6,red0):-chosenColour(6,cyan0).
notChosenColour(7,red0):-chosenColour(7,cyan0).
notChosenColour(8,red0):-chosenColour(8,cyan0).
notChosenColour(9,red0):-chosenColour(9,cyan0).
notChosenColour(4,red0):-chosenColour(4,green0).
notChosenColour(5,red0):-chosenColour(5,green0).
notChosenColour(6,red0):-chosenColour(6,green0).
notChosenColour(7,red0):-chosenColour(7,green0).
notChosenColour(8,red0):-chosenColour(8,green0).
notChosenColour(9,red0):-chosenColour(9,green0).
notChosenColour(5,red0):-chosenColour(5,yellow0).
notChosenColour(6,red0):-chosenColour(6,yellow0).
notChosenColour(7,red0):-chosenColour(7,yellow0).
notChosenColour(8,red0):-chosenColour(8,yellow0).
notChosenColour(9,red0):-chosenColour(9,yellow0).
notChosenColour(5,yellow0):-chosenColour(5,blue0).
notChosenColour(6,yellow0):-chosenColour(6,blue0).
notChosenColour(7,yellow0):-chosenColour(7,blue0).
notChosenColour(8,yellow0):-chosenColour(8,blue0).
notChosenColour(9,yellow0):-chosenColour(9,blue0).
notChosenColour(5,yellow0):-chosenColour(5,cyan0).
notChosenColour(6,yellow0):-chosenColour(6,cyan0).
notChosenColour(7,yellow0):-chosenColour(7,cyan0).
notChosenColour(8,yellow0):-chosenColour(8,cyan0).
notChosenColour(9,yellow0):-chosenColour(9,cyan0).
notChosenColour(5,yellow0):-chosenColour(5,green0).
notChosenColour(6,yellow0):-chosenColour(6,green0).
notChosenColour(7,yellow0):-chosenColour(7,green0).
notChosenColour(8,yellow0):-chosenColour(8,green0).
notChosenColour(9,yellow0):-chosenColour(9,green0).
notChosenColour(5,yellow0):-chosenColour(5,red0).
notChosenColour(6,yellow0):-chosenColour(6,red0).
notChosenColour(7,yellow0):-chosenColour(7,red0).
notChosenColour(8,yellow0):-chosenColour(8,red0).
notChosenColour(9,yellow0):-chosenColour(9,red0).
notChosenColour(6,blue0):-chosenColour(2,blue0).
notChosenColour(6,cyan0):-chosenColour(2,cyan0).
notChosenColour(5,blue0):-chosenColour(3,blue0).
notChosenColour(5,cyan0):-chosenColour(3,cyan0).
notChosenColour(5,green0):-chosenColour(3,green0).
notChosenColour(6,blue0):-chosenColour(3,blue0).
notChosenColour(6,cyan0):-chosenColour(3,cyan0).
notChosenColour(6,green0):-chosenColour(3,green0).
colored(1):-chosenColour(1,blue0).
colored(2):-chosenColour(2,blue0).
colored(3):-chosenColour(3,blue0).
colored(4):-chosenColour(4,blue0).
colored(5):-chosenColour(5,blue0).
colored(6):-chosenColour(6,blue0).
colored(7):-chosenColour(7,blue0).
colored(8):-chosenColour(8,blue0).
colored(9):-chosenColour(9,blue0).
colored(2):-chosenColour(2,cyan0).
colored(3):-chosenColour(3,cyan0).
colored(4):-chosenColour(4,cyan0).
colored(5):-chosenColour(5,cyan0).
colored(6):-chosenColour(6,cyan0).
colored(7):-chosenColour(7,cyan0).
colored(8):-chosenColour(8,cyan0).
colored(9):-chosenColour(9,cyan0).
colored(3):-chosenColour(3,green0).
colored(4):-chosenColour(4,green0).
colored(5):-chosenColour(5,green0).
colored(6):-chosenColour(6,green0).
colored(7):-chosenColour(7,green0).
colored(8):-chosenColour(8,green0).
colored(9):-chosenColour(9,green0).
colored(4):-chosenColour(4,red0).
colored(5):-chosenColour(5,red0).
colored(6):-chosenColour(6,red0).
colored(7):-chosenColour(7,red0).
colored(8):-chosenColour(8,red0).
colored(9):-chosenColour(9,red0).
colored(5):-chosenColour(5,yellow0).
colored(6):-chosenColour(6,yellow0).
colored(7):-chosenColour(7,yellow0).
colored(8):-chosenColour(8,yellow0).
colored(9):-chosenColour(9,yellow0).
:-not colored(1).
:-not colored(2).
:-not colored(3).
:-not colored(4).
:-not colored(5).
:-not colored(6).
:-not colored(7).
:-not colored(8).
:-not colored(9).
