/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import formula.Formula;

/**
 *
 * @author Yizheng
 */
public class Inclusion extends Formula {

	public Inclusion() {
		super();
	}

	public Inclusion(Formula subsumee, Formula subsumer) {
		super(2);
		this.setSubFormulas(subsumee, subsumer);
	}

	@Override
	public String toString() {
		Formula subsumee = this.getSubFormulas().get(0);
		Formula subsumer = this.getSubFormulas().get(1);
		return subsumee + " \u2291 " + subsumer;
	}

}
