package ProgrammingProject;

public class LocalPlayer {

    private String name;

    public LocalPlayer(String name){
        this.name = name;
    }

    public String getName(){
        return name;
    }

    public Move determineMove(DotsAndBoxesGame game) {

        for (int field = 0; field < Board.DIM * Board.DIM; field++) {
            if (!game.getBoard().isFilled(field)) {
                return new Move(field);
            }
        }

        return null;
    }


    public String toString(){
        return "Local Player: " + name;
    }
}
