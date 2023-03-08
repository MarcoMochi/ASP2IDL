chosenColour(3,blue0):-not notChosenColour(3,blue0).
chosenColour(3,green0):-not notChosenColour(3,green0).
notChosenColour(3,blue0):-chosenColour(3,green0).
notChosenColour(3,green0):-chosenColour(3,blue0).
colored(3):-chosenColour(3,blue0).
colored(3):-chosenColour(3,green0).
:-not colored(3).