class Thermostat(Module):                                                                                                               
    def types(self):                                                                                                                    
        self.temp = Integer()                                                                                                              
        self.heatOn = bool
        self.heatOff = bool
                                                                                                                                        
    def init(self):                                                                                                                     
        self.temp = 20                                                                                                            
        self.heatOn = True
        self.heatOff = False
                                                                                                                                        
    def next(self):                                                                                                                     
        if self.heatOn:                                                                                                                 
            if self.temp < 22:                                                                                                    
                self.temp = self.temp + 1                                                                                               
            else:                                                                                                                       
                self.heatOn = False
                self.heatOff = True
        elif self.heatOff:                                                                                                              
            if self.temp > 18:                                                                                                    
                self.temp = self.temp - 1                                                                                               
            else:                                                                                                                       
                self.heatOn = True
                self.heatOff = False
                                                                                                                                        
    def specification(self):                                                                                                            
        invariant1 = (self.temp >= 20)                                                                               
        invariant2 = (self.temp <= 22)
        return invariant1 and invariant2 


