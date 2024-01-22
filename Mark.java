package ProgrammingProject;

public class Mark {
    public enum Player{
        EMPTY, BLUE, RED
    }

    private Player player;

    public Mark(Player player){
        this.player = player;
    }

    public Player getPlayer(){
        return player;
    }

    public boolean isEmpty(){
        return player == Player.EMPTY;
    }
}
