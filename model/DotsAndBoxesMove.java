package ProgrammingProject.model;

public class DotsAndBoxesMove implements Move {

    private final Line line;
    private int start;
    private int end;
    private int index;

    public DotsAndBoxesMove(Line line, int start, int end){
        this.line = line;
        this.start = start;
        this.end = end;
    }

    public Line getLine(){
        return line;
    }

    public int getStart(){
        return start;
    }

    public void setStart(int start){
        this.start = start;
    }

    public int getEnd(){
        return end;
    }

    public void setEnd(int end){
        this.end = end;
    }

    public int getIndex(){
        return index;
    }

    public String toString(){
        return start+"-"+end;
    }

}
